-- Prove2me | solution 1 for Algebra.exists_algebra_away_mul_finite_free_faithfullyFlat_finitePresentation_of_isLocalization_powers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/715da11b-d074-5f46-87d5-da4b75ee427d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_algebra_away_mul_finite_free_faithfullyFlat_finitePresentation_of_isLocalization_powers

set_option autoImplicit false

open scoped TensorProduct

namespace FL26

theorem transport
    {Sg A C C' : Type} [CommRing Sg] [CommRing A] [CommRing C] [CommRing C']
    (r' : Sg) [Algebra Sg A] [IsLocalization.Away r' A]
    [Algebra Sg C] [Algebra C C'] [Algebra Sg C'] [IsScalarTower Sg C C']
    [Algebra A C'] [IsScalarTower Sg A C']
    [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r')) C']
    [Module.Finite Sg C] [Module.Free Sg C] [Module.FaithfullyFlat Sg C] [Algebra.FinitePresentation Sg C] :
    Module.Finite A C' ∧ Module.Free A C' ∧ Module.FaithfullyFlat A C' ∧ Algebra.FinitePresentation A C' := by
  have hpo : Algebra.IsPushout Sg C A C' :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers r') A).mp inferInstance
  haveI : Algebra.IsPushout Sg A C C' := hpo.symm
  have e : A ⊗[Sg] C ≃ₐ[A] C' := Algebra.IsPushout.equiv Sg A C C'
  exact ⟨Module.Finite.equiv e.toLinearEquiv, Module.Free.of_equiv e.toLinearEquiv,
    Module.FaithfullyFlat.of_linearEquiv A (A ⊗[Sg] C) e.symm.toLinearEquiv, Algebra.FinitePresentation.equiv e⟩

end FL26

theorem solution
    {S : Type} [CommRing S] (g r : S)
    (C : Type) [CommRing C] [Algebra S C] [Algebra (Localization.Away g) C] [IsScalarTower S (Localization.Away g) C]
    (hfin : Module.Finite (Localization.Away g) C) (hfree : Module.Free (Localization.Away g) C)
    (hff : Module.FaithfullyFlat (Localization.Away g) C) (hfp : Algebra.FinitePresentation (Localization.Away g) C)
    (C' : Type) [CommRing C'] [Algebra S C'] [Algebra C C'] [IsScalarTower S C C']
    [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r)) C'] :
    ∃ (_ : Algebra (Localization.Away (g * r)) C') (_ : IsScalarTower S (Localization.Away (g * r)) C'),
      Module.Finite (Localization.Away (g * r)) C' ∧ Module.Free (Localization.Away (g * r)) C' ∧
      Module.FaithfullyFlat (Localization.Away (g * r)) C' ∧ Algebra.FinitePresentation (Localization.Away (g * r)) C' := by
  classical
  haveI := hfin
  haveI := hfree
  haveI := hff
  haveI := hfp

  obtain ⟨e₀⟩ : Nonempty (Localization.Away (algebraMap S (Localization.Away g) r) ≃ₐ[S] Localization.Away (g * r)) :=
    ⟨IsLocalization.algEquiv (Submonoid.powers (g * r)) _ _⟩
  letI algSgA : Algebra (Localization.Away g) (Localization.Away (g * r)) :=
    (e₀.toRingEquiv.toRingHom.comp
      (algebraMap (Localization.Away g) (Localization.Away (algebraMap S (Localization.Away g) r)))).toAlgebra
  haveI : IsScalarTower S (Localization.Away g) (Localization.Away (g * r)) :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := Localization.Away g) (A := Localization.Away (g * r)) (fun s => by
      show algebraMap S (Localization.Away (g * r)) s =
        e₀ (algebraMap (Localization.Away g) (Localization.Away (algebraMap S (Localization.Away g) r))
          (algebraMap S (Localization.Away g) s))
      rw [← IsScalarTower.algebraMap_apply S (Localization.Away g)
        (Localization.Away (algebraMap S (Localization.Away g) r)) s, AlgEquiv.commutes])
  have e₁ : Localization.Away (algebraMap S (Localization.Away g) r) ≃ₐ[Localization.Away g] Localization.Away (g * r) :=
    AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (fun _ => rfl)
  haveI locA : IsLocalization.Away (algebraMap S (Localization.Away g) r) (Localization.Away (g * r)) :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap S (Localization.Away g) r)) e₁

  letI algSgC' : Algebra (Localization.Away g) C' :=
    ((algebraMap C C').comp (algebraMap (Localization.Away g) C)).toAlgebra
  haveI : IsScalarTower (Localization.Away g) C C' :=
    IsScalarTower.of_algebraMap_eq (R := Localization.Away g) (S := C) (A := C') (fun _ => rfl)
  haveI : IsScalarTower S (Localization.Away g) C' :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := Localization.Away g) (A := C') (fun s => by
      show algebraMap S C' s = algebraMap C C' (algebraMap (Localization.Away g) C (algebraMap S (Localization.Away g) s))
      rw [← IsScalarTower.algebraMap_apply S (Localization.Away g) C s, ← IsScalarTower.algebraMap_apply S C C' s])
  haveI locC' : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers (algebraMap S (Localization.Away g) r))) C' := by
    have hsub : Algebra.algebraMapSubmonoid C (Submonoid.powers (algebraMap S (Localization.Away g) r)) =
        Algebra.algebraMapSubmonoid C (Submonoid.powers r) := by
      rw [Algebra.algebraMapSubmonoid_powers, Algebra.algebraMapSubmonoid_powers,
        ← IsScalarTower.algebraMap_apply S (Localization.Away g) C r]
    rw [hsub]
    infer_instance
  have hu : IsUnit (algebraMap S C' (g * r)) := by
    rw [map_mul]
    refine IsUnit.mul ?_ ?_
    · rw [IsScalarTower.algebraMap_apply S (Localization.Away g) C' g]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map _
    · rw [IsScalarTower.algebraMap_apply S C C' r]
      exact IsLocalization.map_units C'
        (⟨algebraMap S C r, Algebra.mem_algebraMapSubmonoid_of_mem (⟨r, Submonoid.mem_powers r⟩ : Submonoid.powers r)⟩ :
          Algebra.algebraMapSubmonoid C (Submonoid.powers r))
  letI algAC' : Algebra (Localization.Away (g * r)) C' := (IsLocalization.Away.lift (g * r) hu).toAlgebra
  haveI tSAC' : IsScalarTower S (Localization.Away (g * r)) C' :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := Localization.Away (g * r)) (A := C')
      (fun s => (IsLocalization.Away.lift_eq (g * r) hu s).symm)
  haveI : IsScalarTower (Localization.Away g) (Localization.Away (g * r)) C' := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext s
    show algebraMap (Localization.Away g) C' (algebraMap S (Localization.Away g) s) =
      algebraMap (Localization.Away (g * r)) C'
        (algebraMap (Localization.Away g) (Localization.Away (g * r)) (algebraMap S (Localization.Away g) s))
    rw [← IsScalarTower.algebraMap_apply S (Localization.Away g) C' s,
      ← IsScalarTower.algebraMap_apply S (Localization.Away g) (Localization.Away (g * r)) s,
      ← IsScalarTower.algebraMap_apply S (Localization.Away (g * r)) C' s]
  obtain ⟨h1, h2, h3, h4⟩ := FL26.transport (Sg := Localization.Away g) (A := Localization.Away (g * r)) (C := C) (C' := C')
    (algebraMap S (Localization.Away g) r)
  exact ⟨algAC', tSAC', h1, h2, h3, h4⟩

end S_Algebra_exists_algebra_away_mul_finite_free_faithfullyFlat_finitePresentation_of_isLocalization_powers
end P2MW
export P2MW.S_Algebra_exists_algebra_away_mul_finite_free_faithfullyFlat_finitePresentation_of_isLocalization_powers (solution)
