-- Prove2me | solution 1 for AlgebraicGeometry.isIntegrallyClosed_of_flat_geometricallyReduced_of_normal_away_reduced_divisor
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-26T19:52:55.596384+00:00
-- url     : https://prove2.me/submissions/0ade8689-68ab-4dca-ad5e-d0c1376cb523

import Mathlib
import Theorems.Thm_IsIntegrallyClosedIn_of_isReduced_quotient_span_singleton
import Theorems.Thm_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization

universe u
noncomputable section


set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace PhilipponReducedCartierPullback

theorem reduced_quotient_of_geometricallyReduced
    (R A : Type u) [CommRing R] [IsNoetherianRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A]
    [GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    (t : R) [IsReduced (R ⧸ Ideal.span {t})] :
    IsReduced (A ⧸ Ideal.span {algebraMap R A t}) := by
  let S := R ⧸ Ideal.span {t}
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let b := Spec.map (CommRingCat.ofHom (algebraMap R S))
  haveI : Flat f := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : AlgebraicGeometry.IsReduced (Spec (.of S)) :=
    (affine_isReduced_iff (.of S)).mpr inferInstance
  haveI : AlgebraicGeometry.IsReduced (pullback f b : Scheme.{u}) := inferInstance
  let e := pullbackSpecIso R A S
  haveI : AlgebraicGeometry.IsReduced (Spec (.of (A ⊗[R] S))) :=
    isReduced_of_isOpenImmersion e.inv
  haveI : IsReduced (A ⊗[R] S) := (affine_isReduced_iff (.of (A ⊗[R] S))).mp inferInstance
  have hI : (Ideal.span {t}).map (algebraMap R A) = Ideal.span {algebraMap R A t} := by
    rw [Ideal.map_span, Set.image_singleton]
  let eI := (Ideal.quotEquivOfEq hI.symm).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (Ideal.span {t})).toRingEquiv
  exact isReduced_of_injective eI.toRingHom eI.injective

end PhilipponReducedCartierPullback



set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped nonZeroDivisors

namespace PhilipponCartierBoundaryNormality

lemma isIntegrallyClosed_sections_of_stalks
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) [IsDomain Γ(X, U)]
    (hn : ∀ x : X, x ∈ U → IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro P _ hP
  let y : PrimeSpectrum Γ(X, U) := ⟨P, inferInstance⟩
  let S : Type u := X.presheaf.stalk (hU.fromSpec y)
  letI : Algebra Γ(X, U) S := TopCat.Presheaf.algebra_section_stalk X.presheaf
    (⟨hU.fromSpec y, (hU.isoSpec.inv y).property⟩ : U)
  haveI : IsLocalization.AtPrime S P :=
    hU.isLocalization_stalk' y (hU.isoSpec.inv y).property
  haveI : IsIntegrallyClosed S := hn _ (hU.isoSpec.inv y).property
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl S (Localization.AtPrime P)).toRingEquiv

lemma isIntegrallyClosed_of_reduced_principal_divisor
    {A L : Type u} [CommRing A] [IsDomain A] [CommRing L] [IsDomain L]
    [Algebra A L] (t : A) (ht : t ∈ A⁰) [IsLocalization.Away t L]
    [IsIntegrallyClosed L] [IsReduced (A ⧸ Ideal.span {t})] : IsIntegrallyClosed A := by
  letI : IsIntegrallyClosedIn A L :=
    IsIntegrallyClosedIn.of_isReduced_quotient_span_singleton t ht L
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn_of_isLocalization
    (Submonoid.powers t) (Submonoid.powers_le.mpr ht) L

theorem normal_stalks_of_reduced_principal_divisor
    {X : Scheme.{u}} [IsIntegral X] [IsAffine X]
    (t : Γ(X, ⊤)) (ht : t ≠ 0)
    [IsReduced (Γ(X, ⊤) ⧸ Ideal.span {t})]
    (hn : ∀ x : X, x ∈ X.basicOpen t → IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := by
  haveI : Nonempty (X.basicOpen t) := by
    obtain ⟨x, hx⟩ := (X.basicOpen t).ne_bot_iff_nonempty.mp
      (fun h => ht (eq_zero_of_basicOpen_eq_bot t h))
    exact ⟨⟨x, hx⟩⟩
  have hU : IsAffineOpen (X.basicOpen t) := (isAffineOpen_top X).basicOpen t
  haveI : IsIntegrallyClosed Γ(X, X.basicOpen t) :=
    isIntegrallyClosed_sections_of_stalks hU hn
  haveI : IsIntegrallyClosed Γ(X, ⊤) :=
    isIntegrallyClosed_of_reduced_principal_divisor (L := Γ(X, X.basicOpen t))
      t (mem_nonZeroDivisors_of_ne_zero ht)
  intro x
  letI : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  letI := (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
    ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl
    ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors

end PhilipponCartierBoundaryNormality



set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

namespace PhilipponFlatCartierFamilyNormality

theorem isIntegrallyClosed_of_normal_away_reduced_base_divisor
    (R A : Type u) [CommRing R] [IsNoetherianRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [Module.Flat R A]
    [GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    (t : R) (ht : algebraMap R A t ≠ 0)
    [_root_.IsReduced (R ⧸ Ideal.span {t})]
    [IsIntegrallyClosed (Localization.Away (algebraMap R A t))] :
    IsIntegrallyClosed A ∧
      ∀ x : Spec (.of A), IsIntegrallyClosed ((Spec (.of A)).presheaf.stalk x) := by
  let a := algebraMap R A t
  have ha : a ∈ A⁰ := mem_nonZeroDivisors_of_ne_zero ht
  haveI : IsReduced (A ⧸ Ideal.span {a}) :=
    PhilipponReducedCartierPullback.reduced_quotient_of_geometricallyReduced R A t
  haveI : IsDomain (Localization.Away a) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away a)
      (Submonoid.powers_le.mpr ha)
  have hA : IsIntegrallyClosed A :=
    PhilipponCartierBoundaryNormality.isIntegrallyClosed_of_reduced_principal_divisor
      (L := Localization.Away a) a ha
  letI := hA
  refine ⟨hA, fun x => ?_⟩
  letI : Algebra A ((Spec (.of A)).presheaf.stalk x) :=
    (StructureSheaf.toStalk A x).hom.toAlgebra
  haveI : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk x) x.asIdeal := by
    convert! StructureSheaf.IsLocalization.to_stalk A x
  exact isIntegrallyClosed_of_isLocalization ((Spec (.of A)).presheaf.stalk x)
    x.asIdeal.primeCompl x.asIdeal.primeCompl_le_nonZeroDivisors

end PhilipponFlatCartierFamilyNormality


theorem solution
    (R A : Type u) [CommRing R] [IsNoetherianRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [Module.Flat R A]
    [GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    (t : R) (ht : algebraMap R A t ≠ 0)
    [_root_.IsReduced (R ⧸ Ideal.span {t})]
    [IsIntegrallyClosed (Localization.Away (algebraMap R A t))] :
    IsIntegrallyClosed A ∧
      ∀ x : Spec (.of A), IsIntegrallyClosed ((Spec (.of A)).presheaf.stalk x) := by
  exact PhilipponFlatCartierFamilyNormality.isIntegrallyClosed_of_normal_away_reduced_base_divisor R A t ht
