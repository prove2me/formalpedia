-- Prove2me | solution 1 for AlgebraicGeometry.mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/685b99ff-680e-56b9-bb43-3d9dd7165ce5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
universe u
open AlgebraicGeometry CategoryTheory Topology

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Flat t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V)
    (x : T) (hx : ringKrullDim (T.presheaf.stalk x) ≤ 1) : x ∈ V := by
  classical
  by_cases hxs : t.base x = IsLocalRing.closedPoint R
  swap
  · exact hVη x hxs

  have key : ∀ y : T, y ⤳ x → t.base y = IsLocalRing.closedPoint R → y = x := by
    intro y hyx hys
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R

    obtain ⟨𝔮, rfl⟩ : y ∈ Set.range (T.fromSpecStalk x).base := by
      rw [Scheme.range_fromSpecStalk]; exact hyx

    let g : CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).presheaf.stalk (t.base x) :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ (t.base x) trivial
    let φ : CommRingCat.of R ⟶ T.presheaf.stalk x := g ≫ t.stalkMap x
    have hfac : T.fromSpecStalk x ≫ t = Spec.map φ := by
      rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk t, Spec.fromSpecStalk_eq]
    have hbase : t.base ((T.fromSpecStalk x).base 𝔮) = (Spec.map φ).base 𝔮 := by
      rw [← hfac]; rfl
    have hcomap : ((Spec.map φ).base 𝔮).asIdeal = 𝔮.asIdeal.comap φ.hom := rfl

    have hϖ𝔮 : φ.hom ϖ ∈ 𝔮.asIdeal := by
      have h1 : ((Spec.map φ).base 𝔮).asIdeal = IsLocalRing.maximalIdeal R := by
        rw [← hbase, hys]; rfl
      have h2 : ϖ ∈ 𝔮.asIdeal.comap φ.hom := by
        rw [← hcomap, h1]; exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
      exact h2

    have hgreg : IsSMulRegular ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) (g.hom ϖ) := by
      letI : Algebra Γ(Spec (CommRingCat.of R), ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) :=
        ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (t.base x) trivial).hom.toAlgebra
      haveI := (isAffineOpen_top (Spec (CommRingCat.of R))).isLocalization_stalk ⟨t.base x, trivial⟩
      haveI : IsDomain Γ(Spec (CommRingCat.of R), ⊤) :=
        Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
          (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
      have hle := ((isAffineOpen_top (Spec (CommRingCat.of R))).primeIdealOf
        ⟨t.base x, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors
      haveI : IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) :=
        IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
      have hne : g.hom ϖ ≠ 0 := by
        intro h0
        have hinj := IsLocalization.injective ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) hle
        have h0' : algebraMap Γ(Spec (CommRingCat.of R), ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x))
              ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)
            = algebraMap Γ(Spec (CommRingCat.of R), ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) 0 := by
          rw [map_zero]; exact h0
        have := hinj h0'
        exact hϖ.ne_zero ((Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective
          (by rw [map_zero]; exact this))
      exact (IsRegular.of_ne_zero hne).left.isSMulRegular
    haveI hflat : (t.stalkMap x).hom.Flat := Flat.stalkMap t x
    have hreg : IsSMulRegular (T.presheaf.stalk x) (φ.hom ϖ) := by
      letI := (t.stalkMap x).hom.toAlgebra
      haveI : Module.Flat ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) (T.presheaf.stalk x) := hflat
      exact hgreg.of_flat
    have hnzd : φ.hom ϖ ∈ nonZeroDivisors (T.presheaf.stalk x) := by
      rw [mem_nonZeroDivisors_iff]
      refine ⟨fun a ha => hreg ?_, fun a ha => hreg ?_⟩
      · change φ.hom ϖ * a = φ.hom ϖ * 0; rw [mul_zero]; exact ha
      · change φ.hom ϖ * a = φ.hom ϖ * 0; rw [mul_zero, mul_comm]; exact ha

    have hnotmin : 𝔮.asIdeal ∉ minimalPrimes (T.presheaf.stalk x) := fun hmin =>
      Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hmin) hϖ𝔮 hnzd
    haveI : Ring.KrullDimLE 1 (T.presheaf.stalk x) := (Ring.krullDimLE_iff).mpr hx
    have hmax : 𝔮.asIdeal.IsMaximal :=
      ((Ring.krullDimLE_one_iff.mp inferInstance) 𝔮.asIdeal 𝔮.isPrime).resolve_left hnotmin
    have h𝔮 : 𝔮 = IsLocalRing.closedPoint (T.presheaf.stalk x) :=
      PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
    rw [h𝔮, Scheme.fromSpecStalk_closedPoint]

  have hS : IsClosed {y : T | t.base y = IsLocalRing.closedPoint R} :=
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
      (IsLocalRing.maximalIdeal.isMaximal R)).preimage t.base.hom.continuous
  haveI : QuasiSober {y : T // t.base y = IsLocalRing.closedPoint R} :=
    hS.isClosedEmbedding_subtypeVal.quasiSober
  let xs : {y : T // t.base y = IsLocalRing.closedPoint R} := ⟨x, hxs⟩
  have hZ : closure ({xs} : Set {y : T // t.base y = IsLocalRing.closedPoint R}) ∈
      irreducibleComponents {y : T // t.base y = IsLocalRing.closedPoint R} := by
    refine ⟨isIrreducible_singleton.closure, fun W hW hZW => ?_⟩
    have hη := hW.isGenericPoint_genericPoint_closure
    have hxW : xs ∈ closure W := subset_closure (hZW (subset_closure (Set.mem_singleton xs)))
    have hηx : hW.genericPoint ⤳ xs := hη.specializes hxW
    have hηeq : hW.genericPoint = xs :=
      Subtype.ext (key hW.genericPoint.1 (hηx.map continuous_subtype_val) hW.genericPoint.2)
    have hcl : closure W = closure {xs} := by rw [← hηeq]; exact hη.symm
    exact subset_closure.trans hcl.le
  obtain ⟨y, hyZ, hyV⟩ := hVs _ hZ
  have hsp : x ⤳ y.1 := (specializes_iff_mem_closure.mpr hyZ).map continuous_subtype_val
  exact hsp.mem_open V.isOpen hyV

end S_AlgebraicGeometry_mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing
end P2MW
export P2MW.S_AlgebraicGeometry_mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing (solution)
