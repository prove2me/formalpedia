-- Prove2me | solution 1 for AlgebraicGeometry.genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/cdb34012-2045-5458-854f-8b7aaccc14b3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [IsIntegral X]
    {Y : Scheme.{u}} [IsIntegral Y]
    (e₀ : Y ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₀]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    genericPoint Y ∈ (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ U := by

  let ι : Spec (.of K) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let g : Y ⟶ X := e₀ ≫ pullback.fst c ι
  change genericPoint Y ∈ g ⁻¹ᵁ U

  have hηU : genericPoint X ∈ (U : Set X) :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

  let z₀ : ↥(pullback c ι) := e₀ (genericPoint Y)

  have hz : ∀ z : ↥(pullback c ι), c (pullback.fst c ι z) = ι (pullback.snd c ι z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hbot : ∀ w : ↥(Spec (.of K)), (show PrimeSpectrum R from ι w).asIdeal = ⊥ := fun w => by
    change (PrimeSpectrum.comap (algebraMap R K) w).asIdeal = ⊥
    rw [PrimeSpectrum.comap_asIdeal]
    have hw : (show PrimeSpectrum K from w).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    change Ideal.comap (algebraMap R K) (show PrimeSpectrum K from w).asIdeal = ⊥
    rw [hw, Ideal.comap_bot_of_injective _ hinj]

  have hle : (show PrimeSpectrum R from c (genericPoint X)).asIdeal ≤ ⊥ := by
    rw [← hbot (pullback.snd c ι z₀), PrimeSpectrum.asIdeal_le_asIdeal, PrimeSpectrum.le_iff_specializes]
    change c (genericPoint X) ⤳ ι (pullback.snd c ι z₀)
    rw [← hz z₀]
    exact (genericPoint_specializes (pullback.fst c ι z₀)).map c.continuous
  have hcη : c (genericPoint X) = ι (pullback.snd c ι z₀) :=
    PrimeSpectrum.ext ((le_bot_iff.1 hle).trans (hbot _).symm)

  have hrange : genericPoint X ∈ Set.range (pullback.fst c ι) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨pullback.snd c ι z₀, hcη.symm⟩
  obtain ⟨z, hz'⟩ := hrange
  have hgy : g (inv e₀ z) = genericPoint X := by
    change (inv e₀ ≫ e₀ ≫ pullback.fst c ι) z = genericPoint X
    rw [IsIso.inv_hom_id_assoc]
    exact hz'

  have hsp : g (genericPoint Y) ⤳ genericPoint X := hgy ▸ (genericPoint_specializes (inv e₀ z)).map g.continuous
  exact hsp.mem_open U.isOpen hηU

end S_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
end P2MW
export P2MW.S_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap (solution)
