-- Prove2me | solution 1 for AdjoinRoot.exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0bfa691e-3810-5b47-adba-77af75545fc7

import Mathlib
import Theorems.Thm_IsAdicComplete_of_module_finite_free_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete

set_option autoImplicit false

universe u

open IsLocalRing Polynomial

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (f : R[X]) (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))]
    [Algebra.IsSeparable (ResidueField R) (AdjoinRoot (f.map (residue R)))] :
    ∃ (_ : IsLocalRing (AdjoinRoot f)) (_ : IsLocalHom (algebraMap R (AdjoinRoot f))),
      Module.Finite R (AdjoinRoot f) ∧ Module.Free R (AdjoinRoot f) ∧ Algebra.Etale R (AdjoinRoot f) ∧
      IsAdicComplete (maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) ∧
      Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R) = maximalIdeal (AdjoinRoot f) ∧
      Nonempty (ResidueField (AdjoinRoot f) ≃ₐ[ResidueField R] AdjoinRoot (f.map (residue R))) := by
  classical
  set g : (ResidueField R)[X] := f.map (residue R) with hg
  have hfg : Polynomial.map (residue R) f = g := rfl
  set 𝔪 : Ideal R := maximalIdeal R with h𝔪

  let W := AdjoinRoot f
  let pb : PowerBasis R W := AdjoinRoot.powerBasis' hfm
  haveI : Module.Free R W := Module.Free.of_basis pb.basis
  haveI : Module.Finite R W := Module.Finite.of_basis pb.basis
  have hσ : algebraMap R W = AdjoinRoot.of f := AdjoinRoot.algebraMap_eq f
  set J : Ideal W := 𝔪.map (AdjoinRoot.of f) with hJ

  let e1 : (W ⧸ J) ≃+* AdjoinRoot (Polynomial.map (residue R) f) := (AdjoinRoot.quotEquivQuotMap f 𝔪).toRingEquiv
  let e2 : AdjoinRoot (Polynomial.map (residue R) f) ≃ₐ[ResidueField R] AdjoinRoot g :=
    AdjoinRoot.algEquivOfEq (ResidueField R) _ _ hfg
  let eJ : (W ⧸ J) ≃+* AdjoinRoot g := e1.trans e2.toRingEquiv
  haveI hJmax : J.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField (Field.toIsField (AdjoinRoot g)) eJ.toMulEquiv)

  have hc : IsAdicComplete J W := by
    have h := IsAdicComplete.of_module_finite_free_map 𝔪 W
    rwa [hσ] at h
  haveI := hc
  haveI : IsLocalRing W := isLocalRing_of_isAdicComplete_maximal J
  have hmaxJ : maximalIdeal W = J := (IsLocalRing.eq_maximalIdeal hJmax).symm
  have hlocal : IsLocalHom (algebraMap R W) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have haI : a ∈ 𝔪 := (mem_maximalIdeal a).mpr hna
    have : algebraMap R W a ∈ maximalIdeal W := by
      rw [hmaxJ, hσ]
      exact Ideal.mem_map_of_mem _ haI
    exact (mem_maximalIdeal _).mp this ha
  haveI := hlocal

  let ιr : ResidueField W ≃+* AdjoinRoot g := (Ideal.quotEquivOfEq hmaxJ).trans eJ
  have hι : ∀ c : ResidueField R, ιr (algebraMap (ResidueField R) (ResidueField W) c) =
      algebraMap (ResidueField R) (AdjoinRoot g) c := by
    intro c
    obtain ⟨r, rfl⟩ := residue_surjective c
    show eJ (Ideal.quotEquivOfEq hmaxJ (Ideal.Quotient.mk (maximalIdeal W) (algebraMap R W r))) = _
    rw [Ideal.quotEquivOfEq_mk]
    have h1 : (Ideal.Quotient.mk J) (algebraMap R W r) = algebraMap R (W ⧸ J) r := rfl
    have h2 : eJ (algebraMap R (W ⧸ J) r) = algebraMap (ResidueField R) (AdjoinRoot g) (residue R r) := by
      show e2 (AdjoinRoot.quotEquivQuotMap f 𝔪 (algebraMap R (W ⧸ J) r)) = _
      rw [AlgEquiv.commutes]
      have h3 : algebraMap R (AdjoinRoot (Polynomial.map (residue R) f)) r =
          algebraMap (ResidueField R) (AdjoinRoot (Polynomial.map (residue R) f)) (residue R r) :=
        IsScalarTower.algebraMap_apply R (ResidueField R) _ r
      show e2 (algebraMap R (AdjoinRoot (Polynomial.map (residue R) f)) r) = _
      rw [h3, AlgEquiv.commutes]
    rw [h1, h2]
  let ι : ResidueField W ≃ₐ[ResidueField R] AdjoinRoot g := AlgEquiv.ofRingEquiv hι

  haveI : Algebra.IsSeparable (ResidueField R) (ResidueField W) := AlgEquiv.Algebra.isSeparable ι.symm
  have hmapσ : Ideal.map (algebraMap R W) 𝔪 = maximalIdeal W := by rw [hmaxJ, hσ]
  haveI : Algebra.FormallyUnramified R W := Algebra.FormallyUnramified.of_map_maximalIdeal hmapσ
  haveI : Algebra.Etale R W := Algebra.Etale.of_formallyUnramified_of_flat
  refine ⟨inferInstance, hlocal, inferInstance, inferInstance, inferInstance, ?_, hmapσ, ⟨ι⟩⟩
  rw [hmaxJ]; exact hc

end S_AdjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete
end P2MW
export P2MW.S_AdjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete (solution)
