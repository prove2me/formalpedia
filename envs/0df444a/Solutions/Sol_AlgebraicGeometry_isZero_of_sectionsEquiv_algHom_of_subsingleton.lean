-- Prove2me | solution 1 for AlgebraicGeometry.isZero_of_sectionsEquiv_algHom_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c1103d6d-b424-5e74-a0bf-878335df92d8

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isZero_of_sectionsEquiv_algHom_of_subsingleton

set_option autoImplicit false

open TensorProduct CategoryTheory

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme Flat"
namespace ZeroGateAux
p2m_open "AlgebraicGeometry"

theorem zg_core
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra R Ω]
    (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (instM : Module ℤ K) (hflat : letI := instM; Module.Flat ℤ K)
    (hfin : letI := instM; Module.Finite R (R ⊗[ℤ] K))
    (hgen : Subsingleton (K →+* Ω)) :
    Function.Bijective (Bialgebra.counitAlgHom ℤ K) := by
  obtain rfl : instM = Algebra.toModule := Subsingleton.elim _ _
  have hgenA : Subsingleton (K →ₐ[ℤ] Ω) :=
    ⟨fun φ ψ => AlgHom.coe_ringHom_injective (hgen.elim _ _)⟩
  letI instMod : Module ℤ K := Algebra.toModule
  classical
  haveI := hflat; haveI := hfin

  haveI : Module.Flat R (R ⊗[ℤ] K) := inferInstance
  haveI : Module.IsTorsionFree R (R ⊗[ℤ] K) := inferInstance
  haveI : Module.Free R (R ⊗[ℤ] K) := Module.free_of_finite_type_torsion_free'

  have hpts : Nat.card (R ⊗[ℤ] K →ₐ[R] Ω) = 1 := by
    have e : (R ⊗[ℤ] K →ₐ[R] Ω) ≃ (K →ₐ[ℤ] Ω) :=
      { toFun := fun g =>
          { (g.toRingHom.comp
              (Algebra.TensorProduct.includeRight (R := ℤ) (A := R) (B := K)).toRingHom) with
            commutes' := fun n => by
              simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
                MonoidHom.coe_coe, eq_intCast, map_intCast] }
        invFun := fun f => Algebra.TensorProduct.lift (Algebra.ofId R Ω) f (fun _ _ => Commute.all _ _)
        left_inv := fun g => by
          apply Algebra.TensorProduct.ext'
          intro r k
          simp only [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
          change algebraMap R Ω r * g (1 ⊗ₜ[ℤ] k) = g (r ⊗ₜ[ℤ] k)
          rw [← g.commutes r, ← map_mul]
          congr 1
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            Algebra.algebraMap_self, RingHom.id_apply, mul_one]
        right_inv := fun f => by
          ext k
          show (Algebra.TensorProduct.lift (Algebra.ofId R Ω) f (fun _ _ => Commute.all _ _))
              ((1 : R) ⊗ₜ[ℤ] k) = f k
          rw [Algebra.TensorProduct.lift_tmul]
          simp [Algebra.ofId_apply] }
    rw [Nat.card_congr e]
    haveI : Nonempty (K →ₐ[ℤ] Ω) :=
      ⟨(Algebra.ofId ℤ (Ω)).comp (Bialgebra.counitAlgHom ℤ K)⟩
    letI : Unique (K →ₐ[ℤ] Ω) :=
      @Unique.mk' _ (Classical.inhabited_of_nonempty ‹_›) hgenA
    exact Nat.card_unique
  have hrank : Module.finrank R (R ⊗[ℤ] K) = 1 := by
    rw [← HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R (R ⊗[ℤ] K) (Ω), hpts]

  have hεH_surj : Function.Surjective (Coalgebra.counit (R := R) (A := R ⊗[ℤ] K)) := by
    intro r
    exact ⟨algebraMap R (R ⊗[ℤ] K) r, (Bialgebra.counitAlgHom R (R ⊗[ℤ] K)).commutes r⟩
  have hεH_inj : Function.Injective (Coalgebra.counit (R := R) (A := R ⊗[ℤ] K)) := by
    have eR : (R ⊗[ℤ] K) ≃ₗ[R] R :=
      LinearEquiv.ofFinrankEq _ _ (by rw [hrank, Module.finrank_self])
    have h2 : Function.Injective ((Coalgebra.counit (R := R) (A := R ⊗[ℤ] K)) ∘ₗ eR.symm.toLinearMap) :=
      OrzechProperty.injective_of_surjective_of_injective (LinearMap.id) _
        Function.injective_id (hεH_surj.comp eR.symm.surjective)
    intro x y hxy
    have := @h2 (eR x) (eR y) (by simpa using hxy)
    exact eR.injective this

  have hincl : Function.Injective (fun k : K => (1 : R) ⊗ₜ[ℤ] k) := by
    have h1 : Function.Injective ((Algebra.linearMap ℤ R).rTensor K) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (by
        intro a b h; exact Int.cast_injective (α := R) (by simpa using h))
    have h2 : Function.Injective (((Algebra.linearMap ℤ R).rTensor K) ∘ (TensorProduct.lid ℤ K).symm) :=
      h1.comp (TensorProduct.lid ℤ K).symm.injective
    convert h2 using 1
    ext k
    simp

  refine ⟨?_, fun n => ⟨algebraMap ℤ K n, (Bialgebra.counitAlgHom ℤ K).commutes n⟩⟩
  rw [injective_iff_map_eq_zero]
  intro k hk
  apply hincl
  have hH : Coalgebra.counit (R := R) ((1 : R) ⊗ₜ[ℤ] k) = 0 := by
    rw [TensorProduct.counit_tmul]
    have : Coalgebra.counit (R := ℤ) k = 0 := hk
    simp [this]
  have h0 : Coalgebra.counit (R := R) ((1 : R) ⊗ₜ[ℤ] (0 : K)) = 0 := by simp
  simpa using hεH_inj (hH.trans h0.symm)

theorem zg_points (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (hε : Function.Bijective (Bialgebra.counitAlgHom ℤ K))
    (Γ : Type) [CommRing Γ] : Subsingleton (K →+* Γ) := by
  refine ⟨fun φ ψ => ?_⟩
  have hsec : ∀ k : K, algebraMap ℤ K (Bialgebra.counitAlgHom ℤ K k) = k := fun k =>
    hε.1 (by simp)
  ext k
  rw [← hsec k]
  simp only [eq_intCast, map_intCast]

theorem zg_sheaf {C : Type*} [Category C] (J : GrothendieckTopology C)
    (L : Sheaf J AddCommGrpCat)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (hK : ∀ (Γ : Type) [CommRing Γ], Subsingleton (K →+* Γ))
    (ΓU : C → Type) [∀ U, CommRing (ΓU U)]
    (e : ∀ U : C, L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] ΓU U))) :
    Limits.IsZero L := by
  have hsub : ∀ U : C, Subsingleton (L.1.obj (Opposite.op U)) := fun U => by
    haveI : Subsingleton (WithConv (K →ₐ[ℤ] ΓU U)) :=
      ⟨fun a b => by
        have : WithConv.ofConv a = WithConv.ofConv b :=
          AlgHom.coe_ringHom_injective ((hK (ΓU U)).elim _ _)
        simpa using congrArg WithConv.toConv this⟩
    exact (e U).toEquiv.subsingleton
  have hval : Limits.IsZero L.1 := by
    rw [Functor.isZero_iff]
    intro U
    haveI := hsub U.unop
    exact AddCommGrpCat.isZero_of_subsingleton _
  rw [Limits.IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  exact hval.eq_of_src _ _

end AlgebraicGeometry.ZeroGateAux

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_isZero_of_sectionsEquiv_algHom_of_subsingleton.AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory P2MW.S_AlgebraicGeometry_isZero_of_sectionsEquiv_algHom_of_subsingleton.AlgebraicGeometry.ZeroGateAux"

theorem solution
    (p : ℕ) [Fact p.Prime]
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
    (_ : Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgen : Subsingleton (K →ₐ[ℤ] AlgebraicClosure ℚ))
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤)))) :
    Limits.IsZero L := by

  obtain ⟨ℓ, hℓ, hℓp⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p := by
    by_cases hp : p = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, fun h => hp h.symm⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ
  have hgenR : Subsingleton (K →+* AlgebraicClosure ℚ) := ⟨fun f g => by
    have h := hgen.elim
      ({ f with commutes' := fun n => by simp } : K →ₐ[ℤ] AlgebraicClosure ℚ)
      ({ g with commutes' := fun n => by simp } : K →ₐ[ℤ] AlgebraicClosure ℚ)
    exact RingHom.ext fun k => by simpa using AlgHom.congr_fun h k⟩
  have hε := zg_core (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) K _ ‹_› (hff ℓ hℓ hℓp) hgenR
  exact zg_sheaf (smallFppfTopology specInt) L K (zg_points K hε) (fun U : specInt.Fppf => Γ(U.left, ⊤)) e

end S_AlgebraicGeometry_isZero_of_sectionsEquiv_algHom_of_subsingleton
end P2MW
export P2MW.S_AlgebraicGeometry_isZero_of_sectionsEquiv_algHom_of_subsingleton (solution)
