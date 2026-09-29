-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_algEquiv_of_integers_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/abca2f75-2fc3-5cf4-a472-6ed85a9a44ec

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_algEquiv_of_integers_eq

set_option autoImplicit false
set_option maxHeartbeats 4800000

open AlgebraicCurve IsLocalRing

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fb₁ Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
    [Algebra (IsLocalRing.ResidueField A) Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₂]
    (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
    (heq : R₁.integers = R₂.integers) :
    Nonempty (Fb₁ ≃ₐ[IsLocalRing.ResidueField A] Fb₂) := by

  let i₁₂ : ↥R₁.integers →+* ↥R₂.integers :=
    { toFun := fun x => ⟨x.1, heq ▸ x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let i₂₁ : ↥R₂.integers →+* ↥R₁.integers :=
    { toFun := fun x => ⟨x.1, heq.symm ▸ x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ecast : ↥R₁.integers ≃+* ↥R₂.integers :=
    RingEquiv.ofRingHom i₁₂ i₂₁
      (RingHom.ext fun x => Subtype.ext rfl)
      (RingHom.ext fun x => Subtype.ext rfl)
  have hecast_val : ∀ x, ((ecast x : ↥R₂.integers) : F) = (x : F) := fun x => rfl

  let ρ₂ : ↥R₁.integers →+* Fb₂ := R₂.residue.comp ecast.toRingHom
  have hsurjρ₂ : Function.Surjective ρ₂ :=
    R₂.residue_surjective.comp ecast.surjective
  have hkerρ₂ : RingHom.ker ρ₂ = maximalIdeal R₁.integers := by
    have h1 : RingHom.ker ρ₂ = Ideal.comap ecast.toRingHom (RingHom.ker R₂.residue) :=
      RingHom.comap_ker R₂.residue ecast.toRingHom
    rw [h1, R₂.ker_residue]

    exact IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ ecast.surjective)

  let e₁ : (↥R₁.integers ⧸ RingHom.ker R₁.residue) ≃+* Fb₁ :=
    RingHom.quotientKerEquivOfSurjective R₁.residue_surjective
  let e₂ : (↥R₁.integers ⧸ RingHom.ker ρ₂) ≃+* Fb₂ :=
    RingHom.quotientKerEquivOfSurjective hsurjρ₂
  let equo : (↥R₁.integers ⧸ RingHom.ker R₁.residue) ≃+*
      (↥R₁.integers ⧸ RingHom.ker ρ₂) :=
    Ideal.quotEquivOfEq (by rw [R₁.ker_residue, hkerρ₂])
  let φ : Fb₁ ≃+* Fb₂ := e₁.symm.trans (equo.trans e₂)

  have hφ : ∀ x : ↥R₁.integers, φ (R₁.residue x) = ρ₂ x := by
    intro x
    have he₁ : e₁ (Ideal.Quotient.mk _ x) = R₁.residue x := rfl
    have he₂ : e₂ (Ideal.Quotient.mk _ x) = ρ₂ x := rfl
    simp only [φ, RingEquiv.trans_apply]
    rw [show e₁.symm (R₁.residue x) = Ideal.Quotient.mk _ x from
          (e₁.symm_apply_eq.mpr he₁.symm)]
    rw [show equo (Ideal.Quotient.mk (RingHom.ker R₁.residue) x)
          = Ideal.Quotient.mk (RingHom.ker ρ₂) x from Ideal.quotEquivOfEq_mk _ _]
    exact he₂

  refine ⟨AlgEquiv.ofRingEquiv (f := φ) ?_⟩
  intro c
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) c

  let xA : ↥R₁.integers := ⟨algebraMap L F a, (R₁.algebraMap_mem_iff a).mpr a.2⟩
  have hxA₁ : R₁.residue xA = algebraMap (ResidueField A) Fb₁ (IsLocalRing.residue A a) :=
    R₁.residue_algebraMap a
  have hxA₂ : ρ₂ xA = algebraMap (ResidueField A) Fb₂ (IsLocalRing.residue A a) := by

    have : ecast xA = ⟨algebraMap L F a, (R₂.algebraMap_mem_iff a).mpr a.2⟩ :=
      Subtype.ext rfl
    simp only [ρ₂, RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom, this]
    exact R₂.residue_algebraMap a
  rw [← hxA₁, hφ xA, hxA₂]

end S_AlgebraicCurve_RegularProlongation_exists_algEquiv_of_integers_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_algEquiv_of_integers_eq (solution)
