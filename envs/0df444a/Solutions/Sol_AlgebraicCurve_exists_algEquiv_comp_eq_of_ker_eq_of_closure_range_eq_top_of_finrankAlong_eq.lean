-- Prove2me | solution 1 for AlgebraicCurve.exists_algEquiv_comp_eq_of_ker_eq_of_closure_range_eq_top_of_finrankAlong_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/14353523-efd3-5615-8eca-d58b8d9d7814

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_algEquiv_comp_eq_of_ker_eq_of_closure_range_eq_top_of_finrankAlong_eq

set_option autoImplicit false

open AlgebraicCurve

namespace IsoKerGC5

theorem exists_ringHom_apply_eq
    {K R F F' : Type*} [Field K] [CommRing R] [Field F] [Field F']
    [Algebra K R] [Algebra K F] [Algebra K F']
    (α : R →ₐ[K] F) (β : R →ₐ[K] F')
    (hker : RingHom.ker α.toRingHom = RingHom.ker β.toRingHom)
    (hgen : Subfield.closure (Set.range α) = ⊤) :
    ∃ ι₀ : F →+* F', ∀ r, ι₀ (α r) = β r := by
  classical
  let I : Ideal R := RingHom.ker α.toRingHom
  let D := R ⧸ I
  let αbar : D →+* F := RingHom.kerLift α.toRingHom
  have hαbar : Function.Injective αbar := RingHom.kerLift_injective α.toRingHom
  have hαbar_mk : ∀ r, αbar (Ideal.Quotient.mk I r) = α r := fun r =>
    RingHom.kerLift_mk α.toRingHom r
  let βbar : D →+* F' := Ideal.Quotient.lift I β.toRingHom
    (fun a ha => by rw [← RingHom.mem_ker, ← hker]; exact ha)
  have hβbar : Function.Injective βbar :=
    RingHom.lift_injective_of_ker_le_ideal I _ (le_of_eq hker.symm)
  have hβbar_mk : ∀ r, βbar (Ideal.Quotient.mk I r) = β r := fun r =>
    Ideal.Quotient.lift_mk I _ _
  letI : Algebra D F := αbar.toAlgebra
  haveI : FaithfulSMul D F := (faithfulSMul_iff_algebraMap_injective D F).mpr hαbar
  have hcl : Subring.closure (Set.range α) = α.toRingHom.range :=
    Subring.closure_eq_of_le (fun x ⟨r, hr⟩ => ⟨r, hr⟩)
      (fun x ⟨r, hr⟩ => Subring.subset_closure ⟨r, hr⟩)
  haveI : IsFractionRing D F := by
    refine IsFractionRing.of_field D F (fun z => ?_)
    have hz : z ∈ Subfield.closure (Set.range α) := by rw [hgen]; exact Subfield.mem_top z
    rw [Subfield.mem_closure_iff] at hz
    obtain ⟨y, hy, w, hw, rfl⟩ := hz
    rw [hcl] at hy hw
    obtain ⟨r, rfl⟩ := RingHom.mem_range.mp hy
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp hw
    exact ⟨Ideal.Quotient.mk I r, Ideal.Quotient.mk I s, by congr 1⟩
  refine ⟨IsFractionRing.lift hβbar, fun r => ?_⟩
  have hr : (α r : F) = algebraMap D F (Ideal.Quotient.mk I r) := (hαbar_mk r).symm
  rw [hr, IsFractionRing.lift_algebraMap]
  exact hβbar_mk r

end IsoKerGC5

theorem solution
    {K E R F F' : Type*} [Field K] [Field E] [CommRing R] [Field F] [Field F']
    [Algebra K E] [Algebra K R] [Algebra K F] [Algebra K F']
    (j : E →ₐ[K] R) (α : R →ₐ[K] F) (β : R →ₐ[K] F')
    (hker : RingHom.ker α.toRingHom = RingHom.ker β.toRingHom)
    (hgen : Subfield.closure (Set.range α) = ⊤)
    (hfin : FiniteAlong K (α.comp j)) (hfin' : FiniteAlong K (β.comp j))
    (hdeg : finrankAlong K (α.comp j) = finrankAlong K (β.comp j)) :
    ∃ ι : F ≃ₐ[K] F', (ι : F →ₐ[K] F').comp α = β := by
  obtain ⟨ι₀, hι₀⟩ := IsoKerGC5.exists_ringHom_apply_eq α β hker hgen

  have hK : ∀ k : K, ι₀ (algebraMap K F k) = algebraMap K F' k := fun k => by
    rw [← α.commutes k, hι₀, β.commutes k]
  let ιK : F →ₐ[K] F' := ⟨ι₀, hK⟩
  have hιK : ∀ x, ιK x = ι₀ x := fun _ => rfl

  letI instEF : Algebra E F := algebraAlong (α.comp j)
  letI instEF' : Algebra E F' := algebraAlong (β.comp j)
  haveI : Module.Finite E F := hfin
  haveI : Module.Finite E F' := hfin'
  have hdeg' : Module.finrank E F = Module.finrank E F' := hdeg
  let f : F →ₗ[E] F' :=
    { toFun := ι₀
      map_add' := fun x y => ι₀.map_add x y
      map_smul' := fun e x => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        exact hι₀ (j e) }
  have hinj : Function.Injective f := ι₀.injective
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdeg').mp hinj
  refine ⟨AlgEquiv.ofBijective ιK ⟨fun x y h => hinj h, fun y => hsurj y⟩, ?_⟩
  ext r
  exact hι₀ r

end S_AlgebraicCurve_exists_algEquiv_comp_eq_of_ker_eq_of_closure_range_eq_top_of_finrankAlong_eq
end P2MW
export P2MW.S_AlgebraicCurve_exists_algEquiv_comp_eq_of_ker_eq_of_closure_range_eq_top_of_finrankAlong_eq (solution)
