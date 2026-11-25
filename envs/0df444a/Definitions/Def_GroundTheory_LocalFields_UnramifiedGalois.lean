-- Prove2me | Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
-- name    : GroundTheory_LocalFields_UnramifiedGalois
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:34:17.132361+00:00
-- url     : https://prove2.me/theorems/38fae33b-2df6-4f58-8745-ea1c391f2ebd
-- title:
--   Unramified Galois
-- statement:
--   Definitions and structural lemmas for Unramified Galois, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedGalois.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Theorems.Thm_GroundTheory_LocalField_eq_of_pow_eq_one_of_residue_eq
import Theorems.Thm_GroundTheory_LocalField_exists_isPrimitiveRoot_card_residueField_sub_one
import Theorems.Thm_GroundTheory_LocalField_mem_integer_of_pow_eq_one
import Theorems.Thm_GroundTheory_LocalField_natDegree_minpoly_residue_le
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_residueDegree
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_residueDegree_eq_finrank
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel Polynomial IntermediateField
section Generic
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ} {ζ : L}
theorem algebra_adjoin_eq_top_of_adjoin_eq_top (htop : K⟮ζ⟯ = ⊤) : Algebra.adjoin K {ζ} = ⊤ :=
  (IntermediateField.adjoin_eq_top_iff (F := K) (E := L)).mp htop
theorem algEquiv_eq_one_of_apply_eq (htop : K⟮ζ⟯ = ⊤) {σ : L ≃ₐ[K] L} (hσ : σ ζ = ζ) : σ = 1 := by
  have h := AlgHom.ext_of_adjoin_eq_top (algebra_adjoin_eq_top_of_adjoin_eq_top htop)
    (φ₁ := σ.toAlgHom) (φ₂ := AlgHom.id K L) (by simpa using hσ)
  ext x
  exact DFunLike.congr_fun h x
theorem isGalois_of_adjoin_eq_top (hζ : IsPrimitiveRoot ζ m)
    (hm : (m : K) ≠ 0) (htop : K⟮ζ⟯ = ⊤) : IsGalois K L := by
  have : NeZero m := ⟨by rintro rfl; simp at hm⟩
  have : IsCyclotomicExtension {m} K L := by
    rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨ζ, hζ⟩, fun x ↦ ?_⟩
    have hle : Algebra.adjoin K {ζ} ≤ Algebra.adjoin K {b : L | b ^ m = 1} :=
      Algebra.adjoin_mono (by simpa using hζ.pow_eq_one)
    exact hle (by rw [algebra_adjoin_eq_top_of_adjoin_eq_top htop]; trivial)
  exact IsCyclotomicExtension.isGalois {m} K L
end Generic
section PrimitiveResidue
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
theorem isPrimitiveRoot_residue {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {ζ : 𝒪[L]}
    (hζ : IsPrimitiveRoot ζ m) : IsPrimitiveRoot (IsLocalRing.residue 𝒪[L] ζ) m := by
  refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl ↦ hζ.dvd_of_pow_eq_one l ?_⟩
  refine eq_of_pow_eq_one_of_residue_eq hm ?_ (one_pow m) (by rw [map_pow, hl, map_one])
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
theorem natCast_ne_zero_of_residueField {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) : (m : L) ≠ 0 := by
  intro h
  apply hm
  have : (m : 𝒪[L]) = 0 := Subtype.ext (by simpa using h)
  rw [← map_natCast (IsLocalRing.residue 𝒪[L]), this, map_zero]
end PrimitiveResidue
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
section Residue
variable (L) in

theorem natCast_residueField_ne_zero {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) : (m : 𝓀[L]) ≠ 0 := by
  rw [← map_natCast (algebraMap 𝓀[K] 𝓀[L])]
  exact (map_ne_zero_iff _ (algebraMap 𝓀[K] 𝓀[L]).injective).mpr hm
end Residue
section Cyclotomic
variable {m : ℕ} {ζ : L}
def rootInteger (hm : m ≠ 0) (hζ : ζ ^ m = 1) : 𝒪[L] :=
  ⟨ζ, mem_integer_of_pow_eq_one hm hζ⟩
variable (K L) in

theorem residueAlgEquiv_injective_of_adjoin_eq_top (hm : (m : 𝓀[K]) ≠ 0) (hζ : ζ ^ m = 1)
    (htop : K⟮ζ⟯ = ⊤) : Function.Injective (residueAlgEquiv K L) := by
  have hmL := natCast_residueField_ne_zero L hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply algEquiv_eq_one_of_apply_eq htop
  set z := rootInteger hm0 hζ
  have hz : z ^ m = 1 := Subtype.ext (by simpa [z, rootInteger] using hζ)
  have key : integerAlgEquiv K L σ z = z := by
    refine eq_of_pow_eq_one_of_residue_eq hmL (by rw [← map_pow, hz, map_one]) hz ?_
    rw [← residueAlgEquiv_residue, hσ, AlgEquiv.one_apply]
  simpa [z, rootInteger] using congrArg Subtype.val key
end Cyclotomic
section Unramified
variable (K L)
theorem residueDegree_eq_finrank_of_unramified (h : ramificationIndex K L = 1) :
    residueDegree K L = Module.finrank K L := by
  rw [← ramificationIndex_mul_residueDegree K L, h, one_mul]
theorem exists_isPrimitiveRoot_adjoin_eq_top_of_unramified (h : ramificationIndex K L = 1) :
    ∃ ζ : L, IsPrimitiveRoot ζ (Nat.card 𝓀[L] - 1) ∧ K⟮ζ⟯ = ⊤ := by
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot_card_residueField_sub_one (L := L)
  refine ⟨z, hz.map_of_injective (f := (𝒪[L]).subtype) Subtype.val_injective, ?_⟩
  have hres := isPrimitiveRoot_residue (natCast_card_residueField_sub_one_ne_zero L) hz
  have htop' : 𝓀[K]⟮IsLocalRing.residue 𝒪[L] z⟯ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    by_cases hy : y = 0
    · rw [hy]
      exact zero_mem _
    · have := Fintype.ofFinite 𝓀[L]
      have : NeZero (Nat.card 𝓀[L] - 1) := ⟨fun h0 ↦
        natCast_card_residueField_sub_one_ne_zero L (by rw [h0, Nat.cast_zero])⟩
      have hy1 : y ^ (Nat.card 𝓀[L] - 1) = 1 := by
        rw [Nat.card_eq_fintype_card]
        exact FiniteField.pow_card_sub_one_eq_one y hy
      obtain ⟨i, -, rfl⟩ := hres.eq_pow_of_pow_eq_one hy1
      exact pow_mem (mem_adjoin_simple_self _ _) _
  refine eq_of_le_of_finrank_le le_top ?_
  rw [finrank_top', adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    ← residueDegree_eq_finrank_of_unramified K L h, residueDegree_eq_finrank]
  calc Module.finrank 𝓀[K] 𝓀[L] = Module.finrank 𝓀[K] 𝓀[K]⟮IsLocalRing.residue 𝒪[L] z⟯ := by
        rw [htop', finrank_top']
    _ = (minpoly 𝓀[K] (IsLocalRing.residue 𝒪[L] z)).natDegree :=
        adjoin.finrank (Algebra.IsIntegral.isIntegral _)
    _ ≤ _ := natDegree_minpoly_residue_le z
theorem isGalois_of_unramified (h : ramificationIndex K L = 1) : IsGalois K L := by
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K L h
  have hm := natCast_ne_zero_of_residueField (natCast_card_residueField_sub_one_ne_zero L)
  refine isGalois_of_adjoin_eq_top hζ (fun h0 ↦ hm ?_) htop
  rw [← map_natCast (algebraMap K L), h0, map_zero]
theorem residueAlgEquiv_injective_of_unramified (h : ramificationIndex K L = 1) :
    Function.Injective (residueAlgEquiv K L) := by
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K L h
  have hm := natCast_card_residueField_sub_one_ne_zero L
  refine residueAlgEquiv_injective_of_adjoin_eq_top K L (m := Nat.card 𝓀[L] - 1) (fun h0 ↦ hm ?_)
    hζ.pow_eq_one htop
  rw [← map_natCast (algebraMap 𝓀[K] 𝓀[L]), h0, map_zero]
theorem card_algEquiv_of_unramified (h : ramificationIndex K L = 1) :
    Nat.card (L ≃ₐ[K] L) = Module.finrank K L := by
  have := isGalois_of_unramified K L h
  exact IsGalois.card_aut_eq_finrank K L
theorem residueAlgEquiv_bijective_of_unramified (h : ramificationIndex K L = 1) :
    Function.Bijective (residueAlgEquiv K L) := by
  refine (residueAlgEquiv_injective_of_unramified K L h).bijective_of_nat_card_le ?_
  rw [card_algEquiv_of_unramified K L h, IsGalois.card_aut_eq_finrank, ← residueDegree_eq_finrank,
    residueDegree_eq_finrank_of_unramified K L h]
def galoisEquivResidue (h : ramificationIndex K L = 1) :
    (L ≃ₐ[K] L) ≃* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
  MulEquiv.ofBijective (residueAlgEquiv K L) (residueAlgEquiv_bijective_of_unramified K L h)
def frobenius (h : ramificationIndex K L = 1) : L ≃ₐ[K] L :=
  letI := Fintype.ofFinite 𝓀[K]
  (galoisEquivResidue K L h).symm (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L])
variable {K L}
end Unramified
end GroundTheory.LocalField


