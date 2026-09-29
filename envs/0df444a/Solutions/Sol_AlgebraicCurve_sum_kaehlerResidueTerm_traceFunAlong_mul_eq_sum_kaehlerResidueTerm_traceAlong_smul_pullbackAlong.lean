-- Prove2me | solution 1 for AlgebraicCurve.sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d0ed516a-b294-5eae-8be9-c4e6d027c7e7

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong

set_option autoImplicit false

p2m_open "KaehlerDifferential AlgebraicCurve P2MW.S_AlgebraicCurve_sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong.AlgebraicCurve"
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong Place.restrictAlong Place.fiberAlong Place.mem_fiberAlong SeparableAlong Place HasPrincipalDivisors HasCanonicalLocalResidueKStar kaehlerResidueTerm diagonalHom diagonalHom_apply Differential.pullbackAlong Differential.traceAlong Differential.traceAlong_smul_pullbackAlong traceFunAlong traceFunAlong_apply FibreResidueIdentityAlong"
namespace Theta3Sol
p2m_open "AlgebraicCurve"

p2m_open "KaehlerDifferential AlgebraicCurve P2MW.S_AlgebraicCurve_sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong.AlgebraicCurve"

variable {K F R : Type*} [Field K] [Field F] [Field R] [Algebra K F] [Algebra K R] [HasPrincipalDivisors K R]

theorem pairwiseDisjoint_fiberAlong (φ : F →ₐ[K] R) (hφ : φ.toRingHom.IsIntegral) (S : Finset (Place K F)) :
    (S : Set (Place K F)).PairwiseDisjoint (Place.fiberAlong φ hφ) := by
  intro x _ x' _ hne
  refine Finset.disjoint_left.mpr fun w hw hw' => hne ?_
  rw [Place.mem_fiberAlong] at hw hw'
  exact hw.symm.trans hw'

theorem mem_biUnion_fiberAlong [DecidableEq (Place K R)] (φ : F →ₐ[K] R) (hφ : φ.toRingHom.IsIntegral) (S : Finset (Place K F)) (w : Place K R) :
    w ∈ S.biUnion (Place.fiberAlong φ hφ) ↔ Place.restrictAlong φ hφ w ∈ S := by
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨x, hx, hw⟩
    rw [Place.mem_fiberAlong] at hw
    rwa [hw]
  · intro h
    exact ⟨_, h, Place.mem_fiberAlong.mpr rfl⟩

end AlgebraicCurve.Theta3Sol

open KaehlerDifferential _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong.AlgebraicCurve AlgebraicCurve.Theta3Sol in
theorem solution
    {K F R : Type*} [Field K] [Field F] [Field R] [Algebra K F] [Algebra K R]
    [HasPrincipalDivisors K R] [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K R]
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K R, w.DCoordGenerates] [Nontrivial Ω[F⁄K]] [Nontrivial Ω[R⁄K]]
    (α β : F →ₐ[K] R) (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
    (hFα : FibreResidueIdentityAlong α hα) (hFβ : FibreResidueIdentityAlong β hβ) (hsep : SeparableAlong K β)
    (hΩ : ∀ η : Ω[R⁄K], ∃ (ω₁ : Ω[F⁄K]) (c : R), η = c • Differential.pullbackAlong β ω₁)
    (S : Finset (Place K F))
    (hS : ∀ w : Place K R, Place.restrictAlong α hα w ∈ S ↔ Place.restrictAlong β hβ w ∈ S)
    (g : F) (u : R) (ω : Ω[F⁄K]) :
    ∑ x ∈ S, kaehlerResidueTerm ω (diagonalHom K F (traceFunAlong α (β g * u))) x
      = ∑ z ∈ S, kaehlerResidueTerm (Differential.traceAlong β (u • Differential.pullbackAlong α ω)) (diagonalHom K F g) z := by
  classical

  have step1 : ∀ x ∈ S, kaehlerResidueTerm ω (diagonalHom K F (traceFunAlong α (β g * u))) x
      = ∑ w ∈ Place.fiberAlong α hα x, kaehlerResidueTerm (Differential.pullbackAlong α ω) (diagonalHom K R (β g * u)) w :=
    fun x _ => (hFα x ω (β g * u)).symm
  rw [Finset.sum_congr rfl step1, ← Finset.sum_biUnion (pairwiseDisjoint_fiberAlong α hα S)]

  have hunion : S.biUnion (Place.fiberAlong α hα) = S.biUnion (Place.fiberAlong β hβ) := by
    ext w
    rw [mem_biUnion_fiberAlong (K := K) α hα S w, mem_biUnion_fiberAlong (K := K) β hβ S w, hS]
  rw [hunion, Finset.sum_biUnion (pairwiseDisjoint_fiberAlong β hβ S)]
  refine Finset.sum_congr rfl fun z _ => ?_

  obtain ⟨ω₁, c, hc⟩ := hΩ (u • Differential.pullbackAlong α ω)

  have hterm : ∀ w : Place K R, kaehlerResidueTerm (Differential.pullbackAlong α ω) (diagonalHom K R (β g * u)) w
      = kaehlerResidueTerm (Differential.pullbackAlong β ω₁) (diagonalHom K R (β g * c)) w := by
    intro w
    unfold kaehlerResidueTerm
    have key : u * w.differentialCoeff (Differential.pullbackAlong α ω) = c * w.differentialCoeff (Differential.pullbackAlong β ω₁) := by
      rw [← w.differentialCoeff_smul, ← w.differentialCoeff_smul, hc]
    rw [diagonalHom_apply, diagonalHom_apply, mul_assoc, key, ← mul_assoc]
  rw [Finset.sum_congr rfl fun w _ => hterm w, hFβ z ω₁ (β g * c)]

  have htr : traceFunAlong β (β g * c) = g * traceFunAlong β c := by
    letI := algebraAlong β
    rw [traceFunAlong_apply, traceFunAlong_apply]
    show Algebra.trace F R (algebraMap F R g * c) = g * Algebra.trace F R c
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hTr : Differential.traceAlong β (u • Differential.pullbackAlong α ω) = traceFunAlong β c • ω₁ := by
    rw [hc, Differential.traceAlong_smul_pullbackAlong β hsep c ω₁, traceFunAlong_apply]
  unfold kaehlerResidueTerm
  rw [diagonalHom_apply, diagonalHom_apply, htr, hTr, z.differentialCoeff_smul, mul_assoc]

#print axioms solution

end S_AlgebraicCurve_sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong
end P2MW
export P2MW.S_AlgebraicCurve_sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong (solution)
