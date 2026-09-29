-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/dd3e656e-20f1-56af-8079-ebb3af2750e7

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_TwoChartCech_finrank_ker_baseChange_eq_of_field_extension
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq.AlgebraicGeometry.RelPicard NeronModelInfra"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.exists_sectionsOf_baseChange_equiv_of_locallyTrivial Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "fibreAt fibreModule"
namespace ChiExt
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

open TensorProduct

theorem main
    {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
    {P0 P1 P01 : Type u} [AddCommGroup P0] [Module k P0] [AddCommGroup P1] [Module k P1] [AddCommGroup P01] [Module k P01]
    (r0 : P0 →ₗ[k] P01) (r1 : P1 →ₗ[k] P01)
    {Q0 Q1 Q01 : Type u} [AddCommGroup Q0] [Module k' Q0] [AddCommGroup Q1] [Module k' Q1] [AddCommGroup Q01] [Module k' Q01]
    (s0 : Q0 →ₗ[k'] Q01) (s1 : Q1 →ₗ[k'] Q01)
    (e0 : k' ⊗[k] P0 ≃ₗ[k'] Q0) (e1 : k' ⊗[k] P1 ≃ₗ[k'] Q1) (e01 : k' ⊗[k] P01 ≃ₗ[k'] Q01)
    (h0 : ∀ x, e01 ((r0.baseChange k') x) = s0 (e0 x)) (h1 : ∀ x, e01 ((r1.baseChange k') x) = s1 (e1 x)) :
    Module.finrank k' (LinearMap.ker ((-s0).coprod s1)) = Module.finrank k (LinearMap.ker ((-r0).coprod r1)) ∧
      Module.finrank k' (Q01 ⧸ LinearMap.range ((-s0).coprod s1)) =
        Module.finrank k (P01 ⧸ LinearMap.range ((-r0).coprod r1)) := by
  classical
  set d : P0 × P1 →ₗ[k] P01 := (-r0).coprod r1 with hd
  set d' : Q0 × Q1 →ₗ[k'] Q01 := (-s0).coprod s1 with hd'

  let E : k' ⊗[k] (P0 × P1) ≃ₗ[k'] Q0 × Q1 := TensorProduct.prodRight k k' k' P0 P1 ≪≫ₗ e0.prodCongr e1

  have hsq : ∀ z, e01 ((d.baseChange k') z) = d' (E z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a p =>
      obtain ⟨p0, p1⟩ := p
      have hr0 : e01 (a ⊗ₜ[k] r0 p0) = s0 (e0 (a ⊗ₜ[k] p0)) := by
        have := h0 (a ⊗ₜ[k] p0); rwa [LinearMap.baseChange_tmul] at this
      have hr1 : e01 (a ⊗ₜ[k] r1 p1) = s1 (e1 (a ⊗ₜ[k] p1)) := by
        have := h1 (a ⊗ₜ[k] p1); rwa [LinearMap.baseChange_tmul] at this
      simp only [E, d, d', LinearMap.baseChange_tmul, LinearMap.coprod_apply, LinearMap.neg_apply, LinearEquiv.trans_apply,
        TensorProduct.prodRight_tmul, LinearEquiv.prodCongr_apply, TensorProduct.tmul_add, TensorProduct.tmul_neg, map_add,
        map_neg, hr0, hr1]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcomp : (e01 : k' ⊗[k] P01 →ₗ[k'] Q01) ∘ₗ d.baseChange k' = d' ∘ₗ (E : k' ⊗[k] (P0 × P1) →ₗ[k'] Q0 × Q1) :=
    LinearMap.ext hsq

  have hd'eq : d' = ((e01 : k' ⊗[k] P01 →ₗ[k'] Q01) ∘ₗ d.baseChange k') ∘ₗ (E.symm : Q0 × Q1 →ₗ[k'] k' ⊗[k] (P0 × P1)) := by
    rw [hcomp, LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.comp_id]

  have hker : LinearMap.ker d' = (LinearMap.ker (d.baseChange k')).map (E : k' ⊗[k] (P0 × P1) →ₗ[k'] Q0 × Q1) := by
    rw [hd'eq, LinearMap.ker_comp, LinearMap.ker_comp_of_ker_eq_bot _ e01.ker, Submodule.map_equiv_eq_comap_symm]
  have hfin1 : Module.finrank k' (LinearMap.ker d') = Module.finrank k' (LinearMap.ker (d.baseChange k')) := by
    rw [hker, LinearEquiv.finrank_map_eq]
  have hfin2 : Module.finrank k (LinearMap.ker (d.baseChange k)) = Module.finrank k' (LinearMap.ker (d.baseChange k')) :=
    TwoChartCech.finrank_ker_baseChange_eq_of_field_extension d k k'
  have hlid : LinearMap.ker (d.baseChange k) =
      (LinearMap.ker d).map ((TensorProduct.lid k (P0 × P1)).symm : P0 × P1 →ₗ[k] k ⊗[k] (P0 × P1)) := by
    have hcomp' : d.baseChange k = ((TensorProduct.lid k P01).symm : P01 →ₗ[k] k ⊗[k] P01) ∘ₗ d ∘ₗ
        (TensorProduct.lid k (P0 × P1) : k ⊗[k] (P0 × P1) →ₗ[k] P0 × P1) := by
      apply TensorProduct.ext'
      intro a p
      simp [LinearMap.baseChange_tmul, TensorProduct.lid_tmul, map_smul, TensorProduct.smul_tmul', smul_eq_mul]
    rw [hcomp', LinearMap.ker_comp_of_ker_eq_bot _ (TensorProduct.lid k P01).symm.ker, LinearMap.ker_comp,
      Submodule.comap_equiv_eq_map_symm]
  have hfin3 : Module.finrank k (LinearMap.ker (d.baseChange k)) = Module.finrank k (LinearMap.ker d) := by
    rw [hlid, LinearEquiv.finrank_map_eq]
  refine ⟨by rw [hfin1, ← hfin2, hfin3], ?_⟩

  have hrange : (LinearMap.range (d.baseChange k')).map (e01 : k' ⊗[k] P01 →ₗ[k'] Q01) = LinearMap.range d' := by
    rw [hd'eq, LinearMap.range_comp_of_range_eq_top _ E.symm.range, LinearMap.range_comp]
  have q1 : (Q01 ⧸ LinearMap.range d') ≃ₗ[k'] ((k' ⊗[k] P01) ⧸ LinearMap.range (d.baseChange k')) :=
    (Submodule.Quotient.equiv _ _ e01 hrange).symm
  have hex : Function.Exact (d.baseChange k') ((LinearMap.range d).mkQ.baseChange k') := by
    have h := lTensor_exact k' (LinearMap.exact_map_mkQ_range d) (Submodule.mkQ_surjective _)
    intro y
    have hy := h y
    simp only [LinearMap.baseChange_eq_ltensor, Set.mem_range] at hy ⊢
    exact hy
  have hsurj : Function.Surjective ((LinearMap.range d).mkQ.baseChange k') := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective k' (Submodule.mkQ_surjective _)
  have q2 : ((k' ⊗[k] P01) ⧸ LinearMap.range (d.baseChange k')) ≃ₗ[k'] k' ⊗[k] (P01 ⧸ LinearMap.range d) :=
    hex.linearEquivOfSurjective hsurj
  rw [(q1 ≪≫ₗ q2).finrank_eq, Module.finrank_baseChange]

theorem finrank_H0_eq_and_finrank_H1_eq_baseChange
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (𝒱 : X.TwoAffineOpenCover)
    (M : X.Modules)
    (hM : ∀ p : X, ∃ U : X.Opens, p ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (k' : Type u) [Field k'] [Algebra k k'] :
    Module.finrank k'
        ((𝒱.pullback x k').sectionsOf (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k k'))
          ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k k'))).obj M)).H0 =
      Module.finrank k (𝒱.sectionsOf x M).H0 ∧
    Module.finrank k'
        ((𝒱.pullback x k').sectionsOf (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k k'))
          ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k k'))).obj M)).H1 =
      Module.finrank k (𝒱.sectionsOf x M).H1 := by
  obtain ⟨e0, e1, e01, h0, h1, -, -, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 x M hM k'
  exact main _ _ _ _ e0 e1 e01 h0 h1

theorem twoAffineOpenCover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover} (h0 : 𝒱.U0 = 𝒱'.U0)
    (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  obtain ⟨U0, U1, _, _, _, _⟩ := 𝒱
  obtain ⟨U0', U1', _, _, _, _⟩ := 𝒱'
  cases h0
  cases h1
  rfl

end AlgebraicGeometry.RelPicard.ChiExt

open AlgebraicGeometry.RelPicard.ChiExt

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) (K : Type u) [Field K] [Algebra k K] :
    ∃ 𝒲' : (pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)).TwoAffineOpenCover,
      ∀ (F : (pullback c t).Modules), Scheme.Modules.IsInvertible F →
        Module.finrank K (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s))
            (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F)).H0 =
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 ∧
        Module.finrank K (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s))
            (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F)).H1 =
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 := by

  let ψ : pullback (pullback.snd (pullback.snd c t) s) (Scheme.TwoAffineOpenCover.specMap k K) ≅
      pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s) :=
    pullbackLeftPullbackSndIso (pullback.snd c t) s (Scheme.TwoAffineOpenCover.specMap k K)
  let φ : pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s) ≅
      pullback (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K) := ψ.symm
  have hφx : φ.hom ≫ pullback.snd (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K) =
      fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) := by
    change ψ.inv ≫ pullback.snd (pullback.snd (pullback.snd c t) s) (Scheme.TwoAffineOpenCover.specMap k K) =
      pullback.snd (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_snd _ _ _).symm
  have hφfst : φ.hom ≫ pullback.fst (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K) ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s) := by
    change ψ.inv ≫ pullback.fst (pullback.snd (pullback.snd c t) s) (Scheme.TwoAffineOpenCover.specMap k K) ≫
        pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_fst _ _ _).symm

  obtain ⟨𝒲', hW0, hW1, -, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s))
    (pullback.snd (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K)) φ hφx
    (𝒲.pullback (fibreAt c t s) K)
    (SheafOfModules.unit (pullback (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K)).ringCatSheaf)
    ((Scheme.Modules.pullback φ.hom).obj
      (SheafOfModules.unit (pullback (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K)).ringCatSheaf))
    (Iso.refl _)
  refine ⟨𝒲', fun F hF => ?_⟩

  have hM : Scheme.Modules.IsInvertible (fibreModule c t s F) := hF.pullback _
  obtain ⟨h0, h1⟩ := finrank_H0_eq_and_finrank_H1_eq_baseChange (fibreAt c t s) 𝒲 (fibreModule c t s F) hM.1 K

  let e : fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F ≅ (Scheme.Modules.pullback φ.hom).obj
      ((Scheme.Modules.pullback (pullback.fst (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K))).obj
        (fibreModule c t s F)) :=
    ((Scheme.Modules.pullbackCongr hφfst).app F).symm ≪≫
      ((Scheme.Modules.pullbackComp (φ.hom ≫ pullback.fst (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K))
        (pullback.fst (pullback.snd c t) s)).app F).symm ≪≫
      ((Scheme.Modules.pullbackComp φ.hom (pullback.fst (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K))).app _).symm
  obtain ⟨𝒱, hV0, hV1, ⟨f0⟩, ⟨f1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s))
    (pullback.snd (fibreAt c t s) (Scheme.TwoAffineOpenCover.specMap k K)) φ hφx
    (𝒲.pullback (fibreAt c t s) K) _ _ e
  obtain rfl : 𝒱 = 𝒲' := twoAffineOpenCover_ext (hV0.trans hW0.symm) (hV1.trans hW1.symm)
  exact ⟨f0.finrank_eq.trans h0, f1.finrank_eq.trans h1⟩

end S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq (solution)
