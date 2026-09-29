-- Prove2me | solution 1 for AlgebraicCurve.serrePairing_traceAlong_eq_serrePairing_pullbackAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f156b7f2-e156-5039-b271-377f4fbe1808

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_pullbackAlong

set_option autoImplicit false
set_option maxHeartbeats 1600000

open KaehlerDifferential TensorProduct

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors diagonalHom diagonalHom_apply diagonal_mem_adeleSpace mulAdele mulAdele_apply IsCurveOver IsCurveOver.finrank_kaehler HasCanonicalDivisor HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTerm_support_finite_of_adeleSpace ResidueTheorem regularDifferentials cechH1 kaehlerResidueTerm_zero_left serrePairing serrePairing_apply_mk_eq_finsum_ite algebraAlong isScalarTower_along Place.restrictAlong Place.fiberAlong Place.mem_fiberAlong SeparableAlong Differential.pullbackAlong Differential.traceAlong Differential.traceAlong_smul_pullbackAlong preimage_restrictAlong_union_eq_univ lSpaceOnZero.coe_pullbackAlong_apply cechH1.pullbackAlong cechH1.pullbackAlong_mk traceFunAlong traceFunAlong_apply FibreResidueIdentityAlong"
p2m_open "AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem finsum_eq_finsum_sum_fiberAlong_t2 [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) {M : Type*} [AddCommMonoid M] (g : Place K F' → M)
    (hg : (Function.support g).Finite) :
    ∑ᶠ w, g w = ∑ᶠ v, ∑ w ∈ Place.fiberAlong φ hφ v, g w := by
  classical
  set T := hg.toFinset with hTdef
  have hT : ∀ w, g w ≠ 0 → w ∈ T := fun w hw => hg.mem_toFinset.mpr hw
  have hsub : Function.support g ⊆ (T : Set (Place K F')) := fun w hw => by
    rw [Finset.mem_coe]
    exact hT w hw
  rw [finsum_eq_sum_of_support_subset g hsub]
  have hsupp : (Function.support fun v => ∑ w ∈ Place.fiberAlong φ hφ v, g w)
      ⊆ ((T.image (Place.restrictAlong φ hφ) : Finset (Place K F)) : Set (Place K F)) := by
    intro v hv
    rw [Function.mem_support] at hv
    obtain ⟨w, hw, hgw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
    rw [Finset.coe_image]
    exact ⟨w, by rw [Finset.mem_coe]; exact hT w hgw, Place.mem_fiberAlong.mp hw⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image (Place.restrictAlong φ hφ))
      (g := Place.restrictAlong φ hφ) (fun w hw => Finset.mem_image_of_mem _ hw) g]
  refine Finset.sum_congr rfl fun v _ => ?_
  apply Finset.sum_subset
  · intro w hw
    rw [Finset.mem_filter] at hw
    exact Place.mem_fiberAlong.mpr hw.2
  · intro w hwfib hwT
    by_contra hgw
    exact hwT (Finset.mem_filter.mpr ⟨hT w hgw, Place.mem_fiberAlong.mp hwfib⟩)

section ResidueTermAlgebra

variable {L : Type*} [Field L] [Algebra K L] [HasCanonicalLocalResidueKStar K L]
  [∀ w : Place K L, w.DCoordGenerates] [Nontrivial Ω[L⁄K]]

theorem kaehlerResidueTerm_fsmul_left_t2 (u : L) (η : Ω[L⁄K]) (α : Place K L → L) (w : Place K L) :
    kaehlerResidueTerm (u • η) α w = kaehlerResidueTerm η (mulAdele K u α) w := by
  unfold kaehlerResidueTerm
  rw [w.differentialCoeff_smul, mulAdele_apply, mul_left_comm, mul_assoc]

theorem mulAdele_diagonalHom (u g : L) : mulAdele K u (diagonalHom K L g) = diagonalHom K L (u * g) := by
  funext w
  rw [mulAdele_apply, diagonalHom_apply, diagonalHom_apply]

open Classical in
theorem support_ite_kaehlerResidueTerm_finite_t2 [HasCanonicalDivisor (K := K) (F := L)]
    [HasPrincipalDivisors K L] (S : Set (Place K L)) (η : Ω[L⁄K]) (g : L) :
    (Function.support fun w => if w ∈ S then (0 : K) else kaehlerResidueTerm η (diagonalHom K L g) w).Finite := by
  have hfin : (Function.support (kaehlerResidueTerm η (diagonalHom K L g))).Finite := by
    rcases eq_or_ne η 0 with rfl | hη
    · exact Set.Finite.subset Set.finite_empty fun w hw => hw (kaehlerResidueTerm_zero_left _ w)
    · exact kaehlerResidueTerm_support_finite_of_adeleSpace hη (diagonal_mem_adeleSpace g)
  refine hfin.subset fun w hw => ?_
  rw [Function.mem_support] at hw ⊢
  intro h
  apply hw
  rw [h, ite_self]

end ResidueTermAlgebra

theorem exists_eq_smul_pullbackAlong [IsCurveOver K F'] (φ : F →ₐ[K] F') (hsep : SeparableAlong K φ)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (ω' : Ω[F'⁄K]) :
    ∃ u : F', ω' = u • Differential.pullbackAlong φ ω₀ := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : Algebra.IsSeparable F F' := hsep
  haveI : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  have hequiv : ∀ (u : F') (ω : Ω[F⁄K]),
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F' (u ⊗ₜ ω)
        = u • Differential.pullbackAlong φ ω := by
    intro u ω
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.mapBaseChange_tmul]
    rfl
  have hη₀ : Differential.pullbackAlong φ ω₀ ≠ 0 := by
    intro h
    have h1 : (1 : F') ⊗ₜ[F] ω₀ = 0 := by
      apply (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').injective
      rw [hequiv, one_smul, map_zero, h]
    have hall : ∀ ℓ : Module.Dual F F', ℓ 1 = 0 := by
      intro ℓ
      have h2 := congrArg (fun t => TensorProduct.lid F Ω[F⁄K] (ℓ.rTensor Ω[F⁄K] t)) h1
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_zero] at h2
      exact (smul_eq_zero.mp h2).resolve_right hω₀
    exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff F (1 : F')).mp hall)
  have hspan : Submodule.span F' {Differential.pullbackAlong φ ω₀} = ⊤ :=
    (finrank_eq_one_iff_of_nonzero _ hη₀).mp IsCurveOver.finrank_kaehler
  have hmem : ω' ∈ Submodule.span F' {Differential.pullbackAlong φ ω₀} := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨u, hu.symm⟩

theorem serrePairing_traceAlong_eq_serrePairing_pullbackAlong'
    {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K F']
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] [IsCurveOver K F']
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [HasPrincipalDivisors K F]
    (hRT : ResidueTheorem K F) (hRT' : ResidueTheorem K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hsep : SeparableAlong K φ)
    (hfib : FibreResidueIdentityAlong φ hφ)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (ω' : ↥(regularDifferentials K F'))
    (hω : Differential.traceAlong φ (ω' : Ω[F'⁄K]) ∈ regularDifferentials K F)
    (x : cechH1 S₀ S₁ (0 : Divisor K F)) :
    serrePairing hRT hcover ⟨Differential.traceAlong φ (ω' : Ω[F'⁄K]), hω⟩ x
      = serrePairing hRT' (preimage_restrictAlong_union_eq_univ φ hφ hcover) ω'
          (cechH1.pullbackAlong φ hφ S₀ S₁ x) := by
  classical
  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])
  obtain ⟨u, hu⟩ := exists_eq_smul_pullbackAlong φ hsep hω₀ (ω' : Ω[F'⁄K])
  have htrace : Differential.traceAlong φ (ω' : Ω[F'⁄K])
      = (letI := algebraAlong φ; Algebra.trace F F' u) • ω₀ := by
    rw [hu]
    exact Differential.traceAlong_smul_pullbackAlong φ hsep u ω₀
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [cechH1.pullbackAlong_mk, serrePairing_apply_mk_eq_finsum_ite, serrePairing_apply_mk_eq_finsum_ite,
    lSpaceOnZero.coe_pullbackAlong_apply]
  rw [finsum_eq_finsum_sum_fiberAlong_t2 φ hφ _ (support_ite_kaehlerResidueTerm_finite_t2 _ _ _)]
  refine finsum_congr fun v => ?_
  by_cases hv : v ∈ S₀
  · rw [if_pos hv]
    refine (Finset.sum_eq_zero fun w hw => ?_).symm
    rw [if_pos]
    rw [Set.mem_preimage, Place.mem_fiberAlong.mp hw]
    exact hv
  · rw [if_neg hv]

    have hR : ∑ w ∈ Place.fiberAlong φ hφ v,
        (if w ∈ (Place.restrictAlong φ hφ) ⁻¹' S₀ then (0 : K)
          else kaehlerResidueTerm (ω' : Ω[F'⁄K]) (diagonalHom K F' (φ (f : F))) w)
        = kaehlerResidueTerm ω₀ (diagonalHom K F (traceFunAlong φ (u * φ (f : F)))) v := by
      rw [← hfib v ω₀ (u * φ (f : F))]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [if_neg, hu, kaehlerResidueTerm_fsmul_left_t2, mulAdele_diagonalHom]
      rw [Set.mem_preimage, Place.mem_fiberAlong.mp hw]
      exact hv
    rw [hR]

    show kaehlerResidueTerm (Differential.traceAlong φ (ω' : Ω[F'⁄K])) (diagonalHom K F (f : F)) v = _
    rw [htrace, kaehlerResidueTerm_fsmul_left_t2, mulAdele_diagonalHom]
    congr 2

    letI := algebraAlong φ
    rw [traceFunAlong_apply]
    show Algebra.trace F F' u * (f : F) = Algebra.trace F F' (u * φ (f : F))
    rw [show u * φ (f : F) = (f : F) • u by rw [Algebra.smul_def, mul_comm]; rfl, map_smul, smul_eq_mul,
      mul_comm]

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_pullbackAlong.AlgebraicCurve in
theorem solution
    {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K F']
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] [IsCurveOver K F']
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [HasPrincipalDivisors K F]
    (hRT : ResidueTheorem K F) (hRT' : ResidueTheorem K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hsep : SeparableAlong K φ)
    (hfib : FibreResidueIdentityAlong φ hφ)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (ω' : ↥(regularDifferentials K F'))
    (hω : Differential.traceAlong φ (ω' : Ω[F'⁄K]) ∈ regularDifferentials K F)
    (x : cechH1 S₀ S₁ (0 : Divisor K F)) :
    serrePairing hRT hcover ⟨Differential.traceAlong φ (ω' : Ω[F'⁄K]), hω⟩ x
      = serrePairing hRT' (preimage_restrictAlong_union_eq_univ φ hφ hcover) ω'
          (cechH1.pullbackAlong φ hφ S₀ S₁ x) :=
  serrePairing_traceAlong_eq_serrePairing_pullbackAlong' hRT hRT' φ hφ hsep hfib hcover ω' hω x

end S_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_pullbackAlong
end P2MW
export P2MW.S_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_pullbackAlong (solution)
