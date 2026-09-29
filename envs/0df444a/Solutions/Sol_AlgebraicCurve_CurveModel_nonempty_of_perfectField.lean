-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.nonempty_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5ef7aeae-37f6-56bc-8fd9-7582279c439f

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField

set_option autoImplicit false

universe u v w

noncomputable section

open CategoryTheory AlgebraicGeometry IntermediateField AlgebraicCurve

namespace P2mModelK

theorem nonempty_of_separatingGenerator (K : Type u) [Field K] [PerfectField K] [Infinite K]
    {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)] (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ L] [Algebra.IsSeparable K⟮t⟯ L] : Nonempty (CurveModel K L) := by
  obtain ⟨hpr, hsm, ⟨P, hPb, hPr⟩, haff⟩ := CurveModel.isProper_smooth_places_affineCover_glued K t ht
  haveI := hpr
  haveI := hsm
  exact ⟨{ C := CurveModel.glued K t
           toBase := CurveModel.gluedToBase K t
           ffEquiv := CurveModel.gluedFunctionFieldEquiv K t
           ffEquiv_algebraMap := CurveModel.gluedFunctionFieldEquiv_algebraMap K t
           placeOfPoint := P
           placeOfPoint_bijective := hPb
           range_stalk_eq := hPr
           finset_subset_affineOpen := haff }⟩

section Separating

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

theorem essFiniteType_of_hfg
    (hfg : ∃ x : L, Transcendental K x ∧ FiniteDimensional K⟮x⟯ L) : Algebra.EssFiniteType K L := by
  obtain ⟨x, -, hfin⟩ := hfg
  haveI : Algebra.EssFiniteType K K⟮x⟯ :=
    IntermediateField.essFiniteType_iff.mpr ⟨{x}, by simp⟩
  haveI : Algebra.EssFiniteType K⟮x⟯ L := inferInstance
  exact Algebra.EssFiniteType.comp K K⟮x⟯ L

open scoped _root_.IntermediateField.algebraAdjoinAdjoin in

theorem isTranscendenceBasis_of_hfg {x : L} (hx : Transcendental K x) [FiniteDimensional K⟮x⟯ L] :
    IsTranscendenceBasis K ![x] := by
  refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2
    ⟨algebraicIndependent_iff_transcendental.2 hx, ?_⟩
  have hr : Set.range ![x] = {x} := by
    ext y; simp
  rw [hr]
  haveI : Algebra.IsAlgebraic K⟮x⟯ L := Algebra.IsAlgebraic.of_finite K⟮x⟯ L
  exact Algebra.IsAlgebraic.trans (Algebra.adjoin K ({x} : Set L)) K⟮x⟯ L

end Separating

theorem nonempty_same_universe (K : Type u) [Field K] [PerfectField K] [Infinite K]
    (L : Type u) [Field L] [Algebra K L]
    (hfg : ∃ x : L, Transcendental K x ∧ FiniteDimensional K⟮x⟯ L) : Nonempty (CurveModel K L) := by
  haveI hess := essFiniteType_of_hfg hfg
  obtain ⟨x, hx, hfin⟩ := hfg
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L

  have hxb : IsTranscendenceBasis K ![x] := isTranscendenceBasis_of_hfg hx
  have hcard : s.card = 1 := by
    have h := hxb.lift_cardinalMk_eq hs
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype, Fintype.card_fin, Fintype.card_coe] at h
    norm_num at h
    exact_mod_cast h.symm
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcard
  have ht : Transcendental K t := hs.1.transcendental ⟨t, Finset.mem_singleton_self t⟩
  haveI : Fact (t ≠ 0) := ⟨fun h0 => ht (h0 ▸ isAlgebraic_zero)⟩
  have hcoe : ((({t} : Finset L) : Set L)) = {t} := Finset.coe_singleton t
  haveI hsep' : Algebra.IsSeparable K⟮t⟯ L := by
    rw [hcoe] at hsep
    exact hsep
  haveI : Algebra.IsAlgebraic K⟮t⟯ L := by
    have h := hs.isAlgebraic_field
    have hr : Set.range ((↑) : (({t} : Finset L)) → L) = {t} := by
      ext y; simp
    rw [hr] at h
    exact h
  haveI : Algebra.EssFiniteType K⟮t⟯ L := Algebra.EssFiniteType.of_comp K K⟮t⟯ L
  haveI : FiniteDimensional K⟮t⟯ L := Algebra.finite_of_essFiniteType_of_isAlgebraic
  exact nonempty_of_separatingGenerator K t ht

def congr {K : Type u} [Field K] {L : Type v} {L' : Type w} [Field L] [Field L'] [Algebra K L]
    [Algebra K L'] (e : L' ≃ₐ[K] L) (M : CurveModel K L') : CurveModel K L where
  C := M.C
  toBase := M.toBase
  ffEquiv := e.symm.toRingEquiv.trans M.ffEquiv
  ffEquiv_algebraMap a := by
    change M.ffEquiv (e.symm (algebraMap K L a)) = _
    rw [e.symm.commutes]
    exact M.ffEquiv_algebraMap a
  placeOfPoint x := Place.congrEquiv e.toRingEquiv (fun a => e.commutes a) (M.placeOfPoint x)
  placeOfPoint_bijective :=
    (Place.congrEquiv e.toRingEquiv (fun a => e.commutes a)).bijective.comp M.placeOfPoint_bijective
  range_stalk_eq x := by
    have hM := M.range_stalk_eq x
    have hcomp : ((e.symm.toRingEquiv.trans M.ffEquiv).symm : M.C.functionField ≃+* L).toRingHom.comp
          (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField) =
        (e.toRingEquiv : L' →+* L).comp
          ((M.ffEquiv.symm : M.C.functionField ≃+* L').toRingHom.comp
            (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)) := by
      ext y
      rfl
    rw [hcomp, ← RingHom.map_range, hM, Subring.map_equiv_eq_comap_symm]
    rfl
  finset_subset_affineOpen := M.finset_subset_affineOpen

theorem small_of_hfg {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (hfg : ∃ x : L, Transcendental K x ∧ FiniteDimensional K⟮x⟯ L) : Small.{u} L := by
  obtain ⟨x, hx, hfin⟩ := hfg
  have e1 : K⟮x⟯ ≃ₐ[K] RatFunc K := (RatFunc.algEquivOfTranscendental x hx).symm
  haveI : Small.{u} K⟮x⟯ := small_of_injective e1.injective
  let b := Module.finBasis K⟮x⟯ L
  exact small_of_injective b.equivFun.injective

theorem transcendental_algEquiv {K : Type u} [Field K] {L : Type v} {L' : Type w} [Field L] [Field L']
    [Algebra K L] [Algebra K L'] (e : L' ≃ₐ[K] L) {x : L} (hx : Transcendental K x) :
    Transcendental K (e.symm x) := by
  intro halg
  apply hx
  obtain ⟨p, hp0, hp⟩ := halg
  refine ⟨p, hp0, ?_⟩
  have h := congrArg e hp
  rw [Polynomial.aeval_algHom_apply, map_zero, e.apply_symm_apply] at h
  exact h

theorem finiteDimensional_algEquiv {K : Type u} [Field K] {L : Type v} {L' : Type w} [Field L] [Field L']
    [Algebra K L] [Algebra K L'] (e : L' ≃ₐ[K] L) (x : L) [FiniteDimensional K⟮x⟯ L] :
    FiniteDimensional K⟮e.symm x⟯ L' := by
  have hmap : (K⟮x⟯).map (e.symm : L →ₐ[K] L') = K⟮e.symm x⟯ := by
    rw [adjoin_map]
    simp
  let e₁ : K⟮x⟯ ≃+* K⟮e.symm x⟯ :=
    (((K⟮x⟯).equivMap (e.symm : L →ₐ[K] L')).trans (equivOfEq hmap)).toRingEquiv
  exact Module.Finite.of_equiv_equiv e₁ (e.symm : L ≃ₐ[K] L').toRingEquiv (by ext y; rfl)

theorem main (K : Type u) (L : Type v) [Field K] [PerfectField K] [Infinite K] [Field L] [Algebra K L]
    (hfg : ∃ x : L, Transcendental K x ∧ FiniteDimensional K⟮x⟯ L) :
    Nonempty (CurveModel K L) := by
  haveI := small_of_hfg hfg
  let e : Shrink.{u} L ≃ₐ[K] L := Shrink.algEquiv K L
  have hfg' : ∃ x : Shrink.{u} L, Transcendental K x ∧ FiniteDimensional K⟮x⟯ (Shrink.{u} L) := by
    obtain ⟨x, hx, hfin⟩ := hfg
    exact ⟨e.symm x, transcendental_algEquiv e hx, finiteDimensional_algEquiv e x⟩
  obtain ⟨M⟩ := nonempty_same_universe K (Shrink.{u} L) hfg'
  exact ⟨congr e M⟩

end P2mModelK

end

open AlgebraicCurve

theorem solution
    (K : Type u) (L : Type v) [Field K] [PerfectField K] [Infinite K] [Field L] [Algebra K L]
    (hfg : ∃ x : L, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set L)) L) :
    Nonempty (CurveModel K L) :=
  P2mModelK.main K L hfg

end S_AlgebraicCurve_CurveModel_nonempty_of_perfectField
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField (solution)
