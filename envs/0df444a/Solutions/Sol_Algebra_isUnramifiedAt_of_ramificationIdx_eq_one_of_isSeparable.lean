-- Prove2me | solution 1 for Algebra.isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f829cb44-d417-5cb8-b4d0-c08b1d151b7a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable

set_option autoImplicit false

open IsLocalRing

universe u v

namespace UnramifiedCriterion

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

noncomputable def quotEquiv (p : Ideal R) [p.IsMaximal] : (R ⧸ p) ≃+* p.ResidueField :=
  RingEquiv.ofBijective (algebraMap (R ⧸ p) p.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField p)

theorem quotEquiv_mk (p : Ideal R) [p.IsMaximal] (r : R) :
    quotEquiv p (Ideal.Quotient.mk p r) = algebraMap R p.ResidueField r := by
  change algebraMap (R ⧸ p) p.ResidueField (algebraMap R (R ⧸ p) r) = _
  rw [← IsScalarTower.algebraMap_apply]

theorem main [IsDedekindDomain S] [Algebra.EssFiniteType R S]
    (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hP : P ≠ ⊥)
    (he : p.ramificationIdx' P = 1)
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] : Algebra.IsUnramifiedAt R P := by
  letI := Localization.AtPrime.algebraOfLiesOver p P
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  rw [Algebra.isUnramifiedAt_iff_map_eq R p P]
  refine ⟨?_, (Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff hP ?_).mp he⟩
  ·
    letI : Field (R ⧸ p) := Ideal.Quotient.field p
    letI : Field (S ⧸ P) := Ideal.Quotient.field P
    refine Algebra.IsSeparable.of_equiv_equiv (A₁ := R ⧸ p) (B₁ := S ⧸ P) (A₂ := p.ResidueField)
      (B₂ := P.ResidueField) (quotEquiv p) (quotEquiv P) ?_
    apply Ideal.Quotient.ringHom_ext
    ext r
    simp only [RingHom.comp_apply]
    change algebraMap p.ResidueField P.ResidueField (quotEquiv p (Ideal.Quotient.mk p r)) =
      quotEquiv P (algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p r))
    rw [quotEquiv_mk]
    have h1 : algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p r) =
        Ideal.Quotient.mk P (algebraMap R S r) := rfl
    rw [h1, quotEquiv_mk, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S]
  · rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (Ideal.LiesOver.over (p := p) (P := P))

end UnramifiedCriterion

theorem solution
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsDedekindDomain S] [Algebra.EssFiniteType R S]
    (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hP : P ≠ ⊥)
    (he : p.ramificationIdx' P = 1) [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Algebra.IsUnramifiedAt R P :=
  UnramifiedCriterion.main p P hP he

end S_Algebra_isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable
end P2MW
export P2MW.S_Algebra_isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable (solution)
