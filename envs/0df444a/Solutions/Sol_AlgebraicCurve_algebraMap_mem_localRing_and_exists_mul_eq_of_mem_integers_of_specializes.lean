-- Prove2me | solution 1 for AlgebraicCurve.algebraMap_mem_localRing_and_exists_mul_eq_of_mem_integers_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3606e48f-7057-585b-a08e-8ac318b5d968

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_algebraMap_mem_localRing_and_exists_mul_eq_of_mem_integers_of_specializes

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x) (hxs : x ∈ toBase.smoothLocus)
    (η : X) (hηx : η ⤳ x) (hne : η ≠ x) (hη : toBase.base η = closedPoint ↥A)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η) :
    let S : Subring F := SemistableModel.localRing X φ x
    (∀ a : ↥A, algebraMap L F (a : L) ∈ S) ∧
    (∀ f : F, f ∈ R.integers → ∃ g h : F, g ∈ S ∧ h ∈ S ∧ h ≠ 0 ∧ h⁻¹ ∈ R.integers ∧ f * h = g) := by
  intro S
  classical

  let θ : ∀ y : X, X.presheaf.stalk y →+* F := fun y =>
    (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk y) X.functionField)
  have hθmem : ∀ (y : X) (s : X.presheaf.stalk y), θ y s ∈ SemistableModel.localRing X φ y := fun y s => ⟨s, rfl⟩
  have hθsurj : ∀ (y : X) (f : F), f ∈ SemistableModel.localRing X φ y → ∃ s, θ y s = f := fun y f hf => hf
  have hθinj : ∀ y : X, Function.Injective (θ y) := fun y =>
    φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk y) X.functionField)

  have hθgerm : ∀ (U : X.Opens) (y : X) (hy : y ∈ U) (s : Γ(X, U)),
      θ y ((X.presheaf.germ U y hy).hom s) = φ.symm ((X.germToFunctionField U (h := ⟨⟨y, hy⟩⟩)).hom s) := by
    intro U y hy s
    show φ.symm ((X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
      ((X.presheaf.germ U y hy).hom s)) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  refine ⟨?_, ?_⟩
  ·
    intro a
    have h1 : θ x ((X.presheaf.germ ⊤ x trivial).hom (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom a))) =
        algebraMap L F (a : L) := by
      apply φ.injective
      rw [hφ]
      show φ (φ.symm ((X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
        ((X.presheaf.germ ⊤ x trivial).hom _))) = _
      rw [RingEquiv.apply_symm_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]
      rfl
    rw [← h1]
    exact hθmem x _
  ·
    intro f hf

    let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
    have hU : IsAffineOpen U := isAffineOpen_opensRange _
    have hxU : x ∈ U := X.affineCover.covers x
    have hηU : η ∈ U := hηx.mem_open U.isOpen hxU

    have hfη : f ∈ SemistableModel.localRing X φ η := by
      rw [← hR]; exact hf
    obtain ⟨sη, hsη⟩ := hθsurj η f hfη

    letI algη : Algebra Γ(X, U) (X.presheaf.stalk η) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨η, hηU⟩
    haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk η) (hU.primeIdealOf ⟨η, hηU⟩).asIdeal :=
      hU.isLocalization_stalk ⟨η, hηU⟩
    obtain ⟨⟨b, m⟩, hbm⟩ := IsLocalization.surj (hU.primeIdealOf ⟨η, hηU⟩).asIdeal.primeCompl sη

    have hgermη : ∀ s : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk η) s = (X.presheaf.germ U η hηU).hom s :=
      fun s => rfl
    have hm0 : (m : Γ(X, U)) ≠ 0 := by
      intro h0
      exact m.2 (by rw [h0]; exact Ideal.zero_mem _)
    refine ⟨θ x ((X.presheaf.germ U x hxU).hom b), θ x ((X.presheaf.germ U x hxU).hom m), hθmem x _, hθmem x _, ?_, ?_, ?_⟩
    ·
      intro h0
      apply hm0
      apply germ_injective_of_isIntegral X x hxU
      rw [map_zero]
      exact hθinj x (by rw [h0, map_zero])
    ·
      obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp (IsLocalization.map_units (X.presheaf.stalk η) m)
      rw [hgermη] at hv
      have hθx_eq : θ x ((X.presheaf.germ U x hxU).hom m) = θ η ((X.presheaf.germ U η hηU).hom m) := by
        rw [hθgerm, hθgerm]
      have hinv : (θ x ((X.presheaf.germ U x hxU).hom m))⁻¹ = θ η v := by
        rw [hθx_eq]
        apply eq_comm.mp
        apply eq_inv_of_mul_eq_one_right
        rw [← map_mul, hv, map_one]
      rw [hinv]
      show θ η v ∈ R.integers
      have : θ η v ∈ R.integers.toSubring := by rw [hR]; exact hθmem η v
      exact this
    ·
      rw [← hsη]
      have e1 : θ x ((X.presheaf.germ U x hxU).hom m) = θ η ((X.presheaf.germ U η hηU).hom m) := by rw [hθgerm, hθgerm]
      have e2 : θ x ((X.presheaf.germ U x hxU).hom b) = θ η ((X.presheaf.germ U η hηU).hom b) := by rw [hθgerm, hθgerm]
      rw [e1, e2, ← map_mul, ← hgermη, ← hgermη, hbm]

end S_AlgebraicCurve_algebraMap_mem_localRing_and_exists_mul_eq_of_mem_integers_of_specializes
end P2MW
export P2MW.S_AlgebraicCurve_algebraMap_mem_localRing_and_exists_mul_eq_of_mem_integers_of_specializes (solution)
