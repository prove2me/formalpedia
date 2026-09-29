-- Prove2me | solution 1 for Algebra.natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/d4cd6a00-93a6-58d6-958d-738d92ca40dd

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Algebra p2m_export "Algebra" "ofId commutes mk algebraMap IsIntegral.of_finite restrictScalars" end Algebra
p2m_open_scoped "Algebra" in
open TensorProduct in

theorem Algebra.natCard_algHom_eq_finrank_of_isReduced_of_isAlgClosed
    (K : Type u) [Field K] [IsAlgClosed K] (L : Type u) [CommRing L] [Algebra K L]
    [Module.Finite K L] [IsReduced L] :
    Nat.card (L →ₐ[K] K) = Module.finrank K L := by
  classical
  haveI : IsArtinianRing L := IsArtinianRing.of_finite K L
  haveI : Fintype (MaximalSpectrum L) := Fintype.ofFinite _

  let e : L ≃ₐ[K] ∀ I : MaximalSpectrum L, L ⧸ I.asIdeal := (IsArtinianRing.equivPi L).restrictScalars K

  have hbij : ∀ I : MaximalSpectrum L, Function.Bijective (algebraMap K (L ⧸ I.asIdeal)) := by
    intro I
    haveI : Algebra.IsIntegral K (L ⧸ I.asIdeal) := Algebra.IsIntegral.of_finite K _
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral

  have hrank : Module.finrank K L = Fintype.card (MaximalSpectrum L) := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
    have : ∀ I : MaximalSpectrum L, Module.finrank K (L ⧸ I.asIdeal) = 1 := by
      intro I
      have := (LinearEquiv.ofBijective (Algebra.linearMap K (L ⧸ I.asIdeal)) (hbij I)).finrank_eq
      rw [Module.finrank_self] at this
      exact this.symm
    simp [this]

  let ρ : ∀ I : MaximalSpectrum L, (L ⧸ I.asIdeal) ≃ₐ[K] K := fun I =>
    (AlgEquiv.ofBijective (Algebra.ofId K (L ⧸ I.asIdeal)) (hbij I)).symm
  let toHom : MaximalSpectrum L → (L →ₐ[K] K) := fun I =>
    ((ρ I : (L ⧸ I.asIdeal) →ₐ[K] K)).comp (Ideal.Quotient.mkₐ K I.asIdeal)
  have hker : ∀ I : MaximalSpectrum L, RingHom.ker (toHom I) = I.asIdeal := by
    intro I
    ext x
    simp only [toHom, RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      EmbeddingLike.map_eq_zero_iff, AlgEquiv.coe_algHom]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hinj : Function.Injective toHom := by
    intro I J h
    apply MaximalSpectrum.ext
    rw [← hker I, ← hker J, h]
  have hsurj : Function.Surjective toHom := by
    intro φ
    have hmax : (RingHom.ker φ).IsMaximal := by
      apply RingHom.ker_isMaximal_of_surjective
      intro k
      exact ⟨algebraMap K L k, φ.commutes k⟩
    refine ⟨⟨RingHom.ker φ, hmax⟩, ?_⟩

    apply AlgHom.ext
    intro x
    set I : MaximalSpectrum L := ⟨RingHom.ker φ, hmax⟩

    obtain ⟨k, hk⟩ := (hbij I).2 (Ideal.Quotient.mk I.asIdeal x)
    have hx : x - algebraMap K L k ∈ RingHom.ker φ := by
      change x - algebraMap K L k ∈ I.asIdeal
      rw [← Ideal.Quotient.eq, ← hk]
      rfl
    have h1 : φ x = k := by
      have := hx
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
      exact this
    have h2 : toHom I x = k := by
      have hx' : x - algebraMap K L k ∈ RingHom.ker (toHom I) := by rw [hker]; exact hx
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hx'
      exact hx'
    rw [h2, h1]
  rw [hrank, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.ofBijective toHom ⟨hinj, hsurj⟩)).symm

open TensorProduct in

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] [IsAlgClosed K]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Flat R B]
    [IsReduced (TensorProduct R K B)] :
    Nat.card (B →ₐ[R] K) = Module.finrank (IsLocalRing.ResidueField R) (TensorProduct R (IsLocalRing.ResidueField R) B) := by
  classical
  haveI : Module.Free R B := Module.free_of_flat_of_isLocalRing
  rw [Module.finrank_baseChange, ← Module.finrank_baseChange (R := K),
    Nat.card_congr (AlgHom.liftEquiv R K B K)]
  exact Algebra.natCard_algHom_eq_finrank_of_isReduced_of_isAlgClosed K (K ⊗[R] B)

end S_Algebra_natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced
end P2MW
export P2MW.S_Algebra_natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced (solution)
