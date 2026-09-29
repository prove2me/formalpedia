-- Prove2me | solution 1 for Algebra.FormallyUnramified.algEquiv_apply_eq_of_mem_inertiaSubgroupIn_padicIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/03d2ff29-ca61-532a-b9d3-0b620ecc60f7

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_AlgHom_eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified
import Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallyUnramified_algEquiv_apply_eq_of_mem_inertiaSubgroupIn_padicIntegers

set_option autoImplicit false

open scoped PadicInt NNReal

universe v

theorem solution (p : ℕ) [Fact p.Prime]
    (B : Type v) [CommRing B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B]
    [Algebra.FormallyUnramified ℤ_[p] B]
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p])
    (h : B →ₐ[ℤ_[p]] PadicAlgCl p) (y : B) : σ (h y) = h y := by
  classical

  obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hσ
  change (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (h y) = h y
  have hτ1 : MulSemiringAction.toRingAut (↥((padicIntegers p).decompositionSubgroup ℚ_[p]))
      (IsLocalRing.ResidueField ↥(padicIntegers p)) τ = 1 := MonoidHom.mem_ker.mp hτ
  have hτres : ∀ r : IsLocalRing.ResidueField ↥(padicIntegers p), τ • r = r := fun r =>
    DFunLike.congr_fun hτ1 r

  have hmemO : ∀ x : PadicAlgCl p, IsIntegral ℤ_[p] x → x ∈ padicIntegers p := by
    intro x hx
    rw [mem_padicIntegers_iff, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
    exact (PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p x).mp hx
  have hhO : ∀ b : B, h b ∈ padicIntegers p := fun b =>
    hmemO _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[p]) b).map h)
  have halgO : ∀ r : ℤ_[p], algebraMap ℤ_[p] (PadicAlgCl p) r ∈ padicIntegers p := fun r =>
    hmemO _ isIntegral_algebraMap

  letI algO : Algebra ℤ_[p] ↥(padicIntegers p) := ((algebraMap ℤ_[p] (PadicAlgCl p)).codRestrict (padicIntegers p) halgO).toAlgebra
  have algO_apply : ∀ r : ℤ_[p],
      ((algebraMap ℤ_[p] ↥(padicIntegers p) r : ↥(padicIntegers p)) : PadicAlgCl p) = algebraMap ℤ_[p] (PadicAlgCl p) r := fun _ => rfl

  let h' : B →ₐ[ℤ_[p]] ↥(padicIntegers p) :=
    { (h : B →+* PadicAlgCl p).codRestrict (padicIntegers p) hhO with
      commutes' := fun r => Subtype.ext (by
        rw [algO_apply]
        exact h.commutes r) }
  have h'_apply : ∀ b : B, ((h' b : ↥(padicIntegers p)) : PadicAlgCl p) = h b := fun _ => rfl

  have τ_coe : ∀ x : ↥(padicIntegers p), ((τ • x : ↥(padicIntegers p)) : PadicAlgCl p) = (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x :=
    fun _ => rfl
  let τO : ↥(padicIntegers p) →ₐ[ℤ_[p]] ↥(padicIntegers p) :=
    { MulSemiringAction.toRingHom _ ↥(padicIntegers p) τ with
      commutes' := fun r => Subtype.ext (by
        change ((τ • (algebraMap ℤ_[p] ↥(padicIntegers p) r) : ↥(padicIntegers p)) : PadicAlgCl p) = _
        rw [τ_coe, algO_apply, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p),
          AlgEquiv.commutes]) }
  have τO_apply : ∀ x : ↥(padicIntegers p), τO x = τ • x := fun _ => rfl

  have hfg : ∀ b : B, h' b - (τO.comp h') b ∈ IsLocalRing.maximalIdeal ↥(padicIntegers p) := by
    intro b
    rw [← Ideal.Quotient.eq]
    change IsLocalRing.residue ↥(padicIntegers p) (h' b) = IsLocalRing.residue ↥(padicIntegers p) (τ • h' b)
    rw [IsLocalRing.ResidueField.residue_smul, hτres]
  have heq := AlgHom.eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified
    (IsLocalRing.maximalIdeal ↥(padicIntegers p)) (IsLocalRing.maximalIdeal_le_jacobson _) h' (τO.comp h') hfg
  have key : ((h' y : ↥(padicIntegers p)) : PadicAlgCl p) = (((τO.comp h') y : ↥(padicIntegers p)) : PadicAlgCl p) := by rw [← heq]
  rw [h'_apply, AlgHom.comp_apply, τO_apply, τ_coe, h'_apply] at key
  exact key.symm

end S_Algebra_FormallyUnramified_algEquiv_apply_eq_of_mem_inertiaSubgroupIn_padicIntegers
end P2MW
export P2MW.S_Algebra_FormallyUnramified_algEquiv_apply_eq_of_mem_inertiaSubgroupIn_padicIntegers (solution)
