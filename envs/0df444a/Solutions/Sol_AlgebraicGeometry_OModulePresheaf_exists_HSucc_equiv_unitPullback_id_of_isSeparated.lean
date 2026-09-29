-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5023938a-90e1-5f39-9fac-b8b6300072d3

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Theorems.Thm_DoubleComplex_exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation
import Theorems.Thm_DoubleComplex_exists_HTot_transpose_equiv_mk_eq_mk_swap
import Theorems.Thm_DoubleComplex_exists_HTot_equiv_of_levelwise_equiv_pinned
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_unitPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_dTot_eq_single_biAug_unitPullback_sub_single_id
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

universe u

open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.OModulePresheaf.Leray

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (𝔓 𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝔓.ι) (hlam : ∀ w, 𝒲.U w ≤ (𝟙 X) ⁻¹ᵁ 𝔓.U (lam w)) :
    ∃ (e₀ : ↥((OModulePresheaf.unit π).H0 𝔓) ≃ₗ[R] ↥((OModulePresheaf.unit π).H0 𝒲))
      (e : ∀ n : ℕ, (OModulePresheaf.unit π).HSucc 𝔓 n ≃ₗ[R] (OModulePresheaf.unit π).HSucc 𝒲 n),
      (∀ z : ↥((OModulePresheaf.unit π).H0 𝔓),
        ((e₀ z : ↥((OModulePresheaf.unit π).H0 𝒲)) : (OModulePresheaf.unit π).cochain 𝒲 0) =
          OModulePresheaf.unitPullback (πX := π) (𝟙 X) 𝒲 𝔓 lam hlam 0 z.1) ∧
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝔓 (n + 1)))),
        ∃ hz : OModulePresheaf.unitPullback (πX := π) (𝟙 X) 𝒲 𝔓 lam hlam (n + 1) z.1 ∈
            LinearMap.ker ((OModulePresheaf.unit π).d 𝒲 (n + 1)),
          e n (Submodule.Quotient.mk z) = Submodule.Quotient.mk ⟨_, hz⟩) := by
  classical
  suffices H : ∃ (e₀ : ↥((OModulePresheaf.unit (𝟙 X ≫ π)).H0 𝔓) ≃ₗ[R] ↥((OModulePresheaf.unit (𝟙 X ≫ π)).H0 𝒲))
      (e : ∀ n : ℕ, (OModulePresheaf.unit (𝟙 X ≫ π)).HSucc 𝔓 n ≃ₗ[R] (OModulePresheaf.unit (𝟙 X ≫ π)).HSucc 𝒲 n),
      (∀ z : ↥((OModulePresheaf.unit (𝟙 X ≫ π)).H0 𝔓),
        ((e₀ z : ↥((OModulePresheaf.unit (𝟙 X ≫ π)).H0 𝒲)) : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝒲 0) = OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam 0 z.1) ∧
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 (n + 1)))),
        ∃ hz : OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam (n + 1) z.1 ∈ LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝒲 (n + 1)),
          e n (Submodule.Quotient.mk z) = Submodule.Quotient.mk ⟨_, hz⟩) by
    rw [Category.id_comp] at H
    exact H

  have upb_zero : ∀ m : ℕ, OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam m (0 : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝔓 m) = 0 := by
    intro m; funext s
    by_cases hinj : Function.Injective (lam ∘ s.1)
    · rw [unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj, Pi.zero_apply]
      change _ • (X.presheaf.map _).hom ((Scheme.Hom.app (𝟙 X) _).hom (0 : Γ(X, _))) = (0 : Γ(X, _))
      rw [map_zero, map_zero, smul_zero]
    · rw [unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, Pi.zero_apply]
  have hcoc : ∀ (m : ℕ) (z : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝔓 m), (OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 m z = 0 → OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam m z ∈ LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝒲 m) := by
    intro m z hz
    rw [LinearMap.mem_ker, d_unitPullback, hz, upb_zero]

  obtain ⟨hrowsW, hkerW, hinjW⟩ := rows_exact (𝟙 X) π 𝔓 𝒲
  obtain ⟨hrowsP, hkerP, hinjP⟩ := rows_exact (𝟙 X) π 𝒲 𝔓
  obtain ⟨⟨e0W, he0W⟩, hPW⟩ := DoubleComplex.exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)
    (fun m => (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝒲 m) (fun m => (OModulePresheaf.unit (𝟙 X ≫ π)).d 𝒲 m) (fun m => biAug (𝟙 X) π 𝔓 𝒲 m)
    hinjW (fun m => dV_comp_biAug (𝟙 X) π 𝔓 𝒲 m) hkerW hrowsW
  obtain ⟨⟨e0P, he0P⟩, hPP⟩ := DoubleComplex.exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓)
    (fun m => (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝔓 m) (fun m => (OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 m) (fun m => biAug (𝟙 X) π 𝒲 𝔓 m)
    hinjP (fun m => dV_comp_biAug (𝟙 X) π 𝒲 𝔓 m) hkerP hrowsP
  choose eW heW using hPW
  choose eP heP using hPP

  obtain ⟨el, helH, helV, hel⟩ := exists_levelwise_equiv_transpose_id π 𝔓 𝒲
  have hE1 := fun n => DoubleComplex.exists_HTot_equiv_of_levelwise_equiv_pinned (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓) (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)) el helH helV n
  choose E1 hE1' using hE1
  have hE2 := fun n => DoubleComplex.exists_HTot_transpose_equiv_mk_eq_mk_swap (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n
  choose E2 hE2' using hE2
  obtain ⟨hG30, hG3⟩ := exists_dTot_eq_single_biAug_unitPullback_sub_single_id π 𝔓 𝒲 lam hlam

  have hcol : ∀ (m : ℕ) (z : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝔓 m),
      (show biC (𝟙 X) π 𝔓 𝒲 m 0 from el 0 m (biAug (𝟙 X) π 𝒲 𝔓 m z)) =
        fun στ : BiIdx 𝔓 𝒲 m 0 => (X.presheaf.map (homOfLE ((inf_le_right :
          biOpen (𝟙 X) 𝔓 𝒲 m 0 στ.1 στ.2 ≤ (𝟙 X) ⁻¹ᵁ 𝔓.inter στ.1).trans (Scheme.Hom.id_preimage (𝔓.inter στ.1)).le)).op).hom (z στ.1) := by
    intro m z
    funext στ
    obtain ⟨σ, τ⟩ := στ
    rw [hel 0 m _ σ τ, biAug_apply]
    change ((X.presheaf.map _ ≫ X.presheaf.map _)).hom (z σ) = _
    rw [← Functor.map_comp]
    rfl
  refine ⟨((e0P.trans (E1 0)).trans (E2 0)).trans e0W.symm,
    fun n => (((eP n).trans (E1 (n + 1))).trans (E2 (n + 1))).trans (eW n).symm, ?_, ?_⟩
  ·
    intro z
    have hlz := hcoc 0 z.1 (LinearMap.mem_ker.1 z.2)
    obtain ⟨hEP, h1⟩ := he0P z.1 z.2
    obtain ⟨hc1, h2⟩ := hE1' 0 ⟨_, hEP⟩
    obtain ⟨hS, h3⟩ := hE2' 0 _ hc1
    obtain ⟨hEW, h4⟩ := he0W _ hlz
    have key : e0W.symm (E2 0 (E1 0 (e0P z))) = ⟨_, hlz⟩ := by
      rw [LinearEquiv.symm_apply_eq, show e0P z = e0P ⟨z.1, z.2⟩ from rfl, h1, h2, h3, h4]
      congr 1
      apply Subtype.ext
      funext i
      obtain ⟨⟨p, q⟩, hpq⟩ := i
      obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := ⟨by omega, by omega⟩
      dsimp only
      rw [Pi.single_eq_same, Pi.single_eq_same, Nat.mul_zero, pow_zero, one_smul]
      exact (hcol 0 z.1).trans (hG30 z).symm
    change (((e0W.symm (E2 0 (E1 0 (e0P z)))) : ↥((OModulePresheaf.unit (𝟙 X ≫ π)).H0 𝒲)) : (OModulePresheaf.unit (𝟙 X ≫ π)).cochain 𝒲 0) = _
    rw [key]
  · intro n z
    have hlz := hcoc (n + 1) z.1 (LinearMap.mem_ker.1 z.2)
    refine ⟨hlz, ?_⟩
    obtain ⟨hEP, h1⟩ := heP n z.1 z.2
    obtain ⟨hc1, h2⟩ := hE1' (n + 1) ⟨_, hEP⟩
    obtain ⟨hS, h3⟩ := hE2' (n + 1) _ hc1
    obtain ⟨hEW, h4⟩ := heW n _ hlz
    obtain ⟨hh, hG3n⟩ := hG3 n z
    change (eW n).symm (E2 (n + 1) (E1 (n + 1) (eP n (Submodule.Quotient.mk z)))) = _
    rw [LinearEquiv.symm_apply_eq, show Submodule.Quotient.mk z = Submodule.Quotient.mk ⟨z.1, z.2⟩ from rfl, h1, h2, h3, h4]

    have hne : ∀ (p q : ℕ) (hpq : p + q = n + 1), q ≠ 0 →
        (⟨(q, p), by omega⟩ : DoubleComplex.Diag (n + 1)) ≠ ⟨(0, n + 1), by omega⟩ ∧
        (⟨(p, q), hpq⟩ : DoubleComplex.Diag (n + 1)) ≠ ⟨(n + 1, 0), by omega⟩ := by
      intro p q hpq hq
      refine ⟨fun h => hq ?_, fun h => hq ?_⟩
      · have := congrArg (fun i : DoubleComplex.Diag (n + 1) => i.1.1) h; simpa using this
      · have := congrArg (fun i : DoubleComplex.Diag (n + 1) => i.1.2) h; simpa using this
    apply (Submodule.Quotient.eq _).2
    change ((_ : DoubleComplex.Tot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) (n + 1)) - _) ∈ LinearMap.range (DoubleComplex.dTot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n)
    refine ⟨-hh, ?_⟩
    rw [map_neg, hG3n, neg_sub]
    congr 1
    funext i
    obtain ⟨⟨p, q⟩, hpq⟩ := i
    dsimp only
    by_cases hq : q = 0
    · subst hq
      obtain rfl : p = n + 1 := by omega
      rw [Pi.single_eq_same, Pi.single_eq_same, Nat.mul_zero, pow_zero, one_smul]
      exact (hcol (n + 1) z.1).symm
    · obtain ⟨hne1, hne2⟩ := hne p q hpq hq
      rw [Pi.single_eq_of_ne hne2, Pi.single_eq_of_ne hne1, map_zero]
      exact (smul_zero _).symm

end S_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated (solution)
