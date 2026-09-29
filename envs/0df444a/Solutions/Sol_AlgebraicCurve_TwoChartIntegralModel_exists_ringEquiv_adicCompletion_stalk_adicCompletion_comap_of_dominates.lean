-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_dominates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7ccb28a1-9ada-5482-b712-ac6c1014ee24

import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_IsLocalization_AtPrime_exists_ringEquiv_adicCompletion_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_dominates

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(XFin R F j))
    (hz : (ιFin R F j).base y ∈ (ιFin R F j) ''ᵁ ⊤)
    (B : Type u) [CommRing B] (κ : B →+* ↥(chartAlgFin R F j)) (hκ : Function.Injective κ)
    (hdom : ∀ c : ↥(chartAlgFin R F j), ∃ b d : B, κ d ∉ y.asIdeal ∧ c * κ d = κ b)
    (hmax : (y.asIdeal.comap κ).IsMaximal) :
    let STK := (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)
    let germY : ↥(chartAlgFin R F j) →+* STK :=
      (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base y) hz).hom).comp
        (((((ιFin R F j).appIso ⊤).inv).hom).comp
          (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom)
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal STK) STK ≃+* AdicCompletion (y.asIdeal.comap κ) B,
      ∀ b : B, e (algebraMap STK (AdicCompletion (IsLocalRing.maximalIdeal STK) STK) (germY (κ b))) =
        algebraMap B (AdicCompletion (y.asIdeal.comap κ) B) b := by
  intro STK germY
  classical
  set 𝔪 : Ideal B := y.asIdeal.comap κ with h𝔪
  haveI h𝔪max : 𝔪.IsMaximal := hmax

  letI algC1 : Algebra ↥(chartAlgFin R F j) ((XFin R F j).presheaf.stalk y) :=
    StructureSheaf.stalkAlgebra ↥(chartAlgFin R F j) y
  haveI hloc1 : IsLocalization.AtPrime ((XFin R F j).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk ↥(chartAlgFin R F j) y

  haveI : IsIso ((ιFin R F j).stalkMap y) := inferInstance
  let τ : STK ≃+* (XFin R F j).presheaf.stalk y := (asIso ((ιFin R F j).stalkMap y)).commRingCatIsoToRingEquiv
  have hτ : ∀ c : ↥(chartAlgFin R F j), τ (germY c) = algebraMap ↥(chartAlgFin R F j) ((XFin R F j).presheaf.stalk y) c := by
    intro c
    show ((ιFin R F j).stalkMap y).hom
      (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base y) hz).hom
        (((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom c))) = _
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply, TopCat.Presheaf.germ_res_apply]
    rfl

  letI algCS : Algebra ↥(chartAlgFin R F j) STK := germY.toAlgebra
  let τa : ((XFin R F j).presheaf.stalk y) ≃ₐ[↥(chartAlgFin R F j)] STK :=
    AlgEquiv.ofRingEquiv (f := τ.symm) (fun c => by
      rw [RingEquiv.symm_apply_eq]; exact (hτ c).symm)
  haveI hlocS : IsLocalization.AtPrime STK y.asIdeal :=
    IsLocalization.isLocalization_of_algEquiv y.asIdeal.primeCompl τa

  letI algBS : Algebra B STK := (germY.comp κ).toAlgebra
  have halgB : ∀ b : B, algebraMap B STK b = algebraMap ↥(chartAlgFin R F j) STK (κ b) := fun b => rfl
  haveI hlocB : IsLocalization.AtPrime STK 𝔪 := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨d, hd⟩
      rw [halgB]
      exact IsLocalization.map_units STK (⟨κ d, hd⟩ : y.asIdeal.primeCompl)
    · intro z
      obtain ⟨⟨c, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective y.asIdeal.primeCompl z
      obtain ⟨b, d, hd, hc⟩ := hdom c
      obtain ⟨b', d', hd', hs'⟩ := hdom s
      have hb' : κ b' ∉ y.asIdeal := by
        rw [← hs']; exact fun h => (y.2.mem_or_mem h).elim hs hd'
      refine ⟨⟨b * d', ⟨d * b', fun h => ?_⟩⟩, ?_⟩
      · have h' : κ (d * b') ∈ y.asIdeal := h
        rw [map_mul] at h'
        exact (y.2.mem_or_mem h').elim hd hb'
      · show IsLocalization.mk' _ c ⟨s, hs⟩ * algebraMap B STK (d * b') = algebraMap B STK (b * d')
        rw [halgB, halgB, map_mul κ, map_mul κ, ← hc, ← hs', map_mul, map_mul, map_mul, map_mul]
        have := IsLocalization.mk'_spec STK c ⟨s, hs⟩
        calc IsLocalization.mk' STK c ⟨s, hs⟩ *
              (algebraMap _ STK (κ d) * (algebraMap _ STK s * algebraMap _ STK (κ d')))
            = (IsLocalization.mk' STK c ⟨s, hs⟩ * algebraMap _ STK s) *
                (algebraMap _ STK (κ d) * algebraMap _ STK (κ d')) := by ring
          _ = algebraMap _ STK c * algebraMap _ STK (κ d) * algebraMap _ STK (κ d') := by rw [this]; ring
    · intro b₁ b₂ h
      rw [halgB, halgB, IsLocalization.eq_iff_exists y.asIdeal.primeCompl] at h
      obtain ⟨⟨s, hs⟩, h⟩ := h
      obtain ⟨b', d', hd', hs'⟩ := hdom s
      have hb' : κ b' ∉ y.asIdeal := by
        rw [← hs']; exact fun h => (y.2.mem_or_mem h).elim hs hd'
      refine ⟨⟨b', hb'⟩, hκ ?_⟩
      show κ (b' * b₁) = κ (b' * b₂)
      have h2 : s * κ b₁ = s * κ b₂ := h
      rw [map_mul, map_mul, ← hs', mul_right_comm, h2, mul_right_comm]

  obtain ⟨ê, hê⟩ := IsLocalization.AtPrime.exists_ringEquiv_adicCompletion_maximalIdeal 𝔪 STK
  exact ⟨ê.symm, fun b => by rw [RingEquiv.symm_apply_eq]; exact (hê b).symm⟩

end S_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_dominates
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_dominates (solution)
