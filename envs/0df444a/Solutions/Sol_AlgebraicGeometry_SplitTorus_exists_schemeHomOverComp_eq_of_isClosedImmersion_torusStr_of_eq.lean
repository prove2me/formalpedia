-- Prove2me | solution 1 for AlgebraicGeometry.SplitTorus.exists_schemeHomOverComp_eq_of_isClosedImmersion_torusStr_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/59206b01-5a07-540d-8dba-b35b2026d50a

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SplitTorus_exists_schemeHomOverComp_eq_of_isClosedImmersion_torusStr_of_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SplitTorus NeronModelInfra

namespace SubtorusRank

theorem injective_of_surjective_of_isNoetherianRing {R : Type*} [CommRing R] [IsNoetherianRing R] (φ : R →+* R)
    (hφ : Function.Surjective φ) : Function.Injective φ := by

  let K : ℕ →o Ideal R :=
    { toFun := fun n => RingHom.ker (φ ^ n)
      monotone' := by
        intro m n hmn x hx
        rw [RingHom.mem_ker] at hx ⊢
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
        rw [add_comm, pow_add, RingHom.coe_mul, Function.comp_apply, hx, map_zero] }
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian (R := R) (M := R)).mpr (isNoetherianRing_iff.mp inferInstance) K
  have hφN : Function.Surjective (φ ^ N) := by
    rw [RingHom.coe_pow]; exact hφ.iterate N
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hφN x
  have hy : y ∈ K (N + 1) := by
    show (φ ^ (N + 1)) y = 0
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, hx]
  rw [← hN (N + 1) (Nat.le_succ N)] at hy
  exact hy

theorem isNoetherianRing_torusCoord (κ : Type) [Field κ] (t : ℕ) : IsNoetherianRing (torusCoord κ t) := by
  haveI : Algebra.FiniteType κ (torusCoord κ t) := AddMonoidAlgebra.finiteType_of_fg κ (Fin t → ℤ)
  exact Algebra.FiniteType.isNoetherianRing κ (torusCoord κ t)

end SubtorusRank

theorem solution
    (κ : Type) [Field κ] [IsAlgClosed κ] (t t' : ℕ) (ht : t' = t)
    (F : SchemeHomOver (torusStr κ t') (torusStr κ t)) (hF : IsClosedImmersion F.1) :
    ∀ y : SchemeHomOver (𝟙 _) (torusStr κ t),
      ∃ z : SchemeHomOver (𝟙 _) (torusStr κ t'), NeronModelInfra.schemeHomOverComp z F = y := by
  subst ht

  obtain ⟨φ0, hφ0⟩ := Spec.map_surjective F.1
  let φ : torusCoord κ t' →+* torusCoord κ t' := φ0.hom
  have hF1 : F.1 = Spec.map (CommRingCat.ofHom φ) := by rw [← hφ0]; rfl
  have hsurjTop : Function.Surjective ((Spec.map (CommRingCat.ofHom φ)).appTop) := by
    have := (IsClosedImmersion.isAffine_surjective_of_isAffine F.1).2
    rwa [hF1] at this
  have hsurj : Function.Surjective φ := by
    have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
    have hbij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (torusCoord κ t'))).hom
    intro s
    obtain ⟨a, ha⟩ := hbij.2 s
    obtain ⟨b, hb⟩ := hsurjTop a
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (torusCoord κ t'))).hom b, ?_⟩
    have h2 := ConcreteCategory.congr_hom hnat b
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
    rw [hb, ha] at h2

    exact h2.symm

  haveI := SubtorusRank.isNoetherianRing_torusCoord κ t'
  have hinj : Function.Injective φ := SubtorusRank.injective_of_surjective_of_isNoetherianRing φ hsurj
  let e : torusCoord κ t' ≃+* torusCoord κ t' := RingEquiv.ofBijective φ ⟨hinj, hsurj⟩
  haveI : IsIso (CommRingCat.ofHom φ) := by
    change IsIso (e.toCommRingCatIso).hom
    infer_instance
  haveI : IsIso F.1 := by rw [hF1]; infer_instance

  intro y
  refine ⟨⟨y.1 ≫ inv F.1, ?_⟩, ?_⟩
  · have h3 : inv F.1 ≫ torusStr κ t' = torusStr κ t' := by
      rw [IsIso.inv_comp_eq]
      exact F.2.symm
    rw [Category.assoc, h3]
    exact y.2
  · apply Subtype.ext
    show (y.1 ≫ inv F.1) ≫ F.1 = y.1
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end S_AlgebraicGeometry_SplitTorus_exists_schemeHomOverComp_eq_of_isClosedImmersion_torusStr_of_eq
end P2MW
export P2MW.S_AlgebraicGeometry_SplitTorus_exists_schemeHomOverComp_eq_of_isClosedImmersion_torusStr_of_eq (solution)
