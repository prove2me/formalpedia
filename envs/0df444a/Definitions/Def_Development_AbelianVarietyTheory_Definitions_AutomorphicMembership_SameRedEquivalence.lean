-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_SameRedEquivalence
-- name    : Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_SameRedEquivalence
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T22:57:05.903048+00:00
-- url     : https://prove2.me/theorems/6a6f4f85-eeaf-4276-b464-860165f8f680
-- title:
--   Same Red Equivalence
-- statement:
--   Definitions and structural lemmas for Same Red Equivalence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/SameRedEquivalence.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinrankLeFinrankInfPerpXPlus
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_SA_IsComp_unique
import Theorems.Thm_GlobalTheory_SA_IsPairMap_fixSp_sup_X
import Theorems.Thm_GlobalTheory_SA_IsSig_unique
import Theorems.Thm_GlobalTheory_SA_IsTransv_disjoint_xPlus
import Theorems.Thm_GlobalTheory_SA_X_le_perp_xPlus
import Theorems.Thm_GlobalTheory_SA_exists_isSig
import Theorems.Thm_GlobalTheory_SA_fixSp_le
import Theorems.Thm_GlobalTheory_SA_isPairMap_refl
import Theorems.Thm_GlobalTheory_SA_norLift_decomp
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_e_cd4c86133218
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_f_95382bea84da
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_k_8a59f7856bba
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_m_92f5719d2794
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_n_ddfb24727e1c
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_order_e93fa31b6760
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_r_6b0f69a7b59a
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_rankComplement_9cb33f905537
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_t_ec1b9c4ed304
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_vertexCount_b44560ac9584
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_wittIndex_e86ea14fff7c
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_e_cd4c86133218
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_f_95382bea84da
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_k_8a59f7856bba
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_m_92f5719d2794
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_n_ddfb24727e1c
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_order_e93fa31b6760
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_r_6b0f69a7b59a
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_rankComplement_9cb33f905537
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_t_ec1b9c4ed304
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_vertexCount_b44560ac9584
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_wittIndex_e86ea14fff7c


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IntPair
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Module
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
def SameRed (F' F'' : FlagD H r) (β β₁ : V ≃ₗ[K] V) : Prop := ∀ x ∈ perp H F'.X, β₁ x - β x ∈ F''.X
def RedMap (F F' F'' : FlagD H r) (Λ : Submodule R V) (g : R) : Type :=
  Quot fun β β₁ : {β : V ≃ₗ[K] V // IsPairMap F F' F'' Λ g β} => SameRed F' F'' β.1 β₁.1
abbrev AutRed (F : FlagD H r) (Λ : Submodule R V) : Type := RedMap F F F Λ 1
def corank (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : ℕ :=
  finrank K (↥(perp H (xPlus F)) ⧸ (fixSp F F' F'' β ⊔ F.X).submoduleOf (perp H (xPlus F)))
def IsScalar (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : Prop :=
  IsTransv F F' ∧ IsTransv F F'' ∧ corank F F' F'' β = 1 ∧
    ∀ y y' a a', IsSig F F' y y' a a' → IsSig F F'' y (β y') a a'
def Carry (s : V ≃ₗ[K] V) (F F₁ : FlagD H r) : Prop :=
  s ∈ isomGrp H ∧ (∀ x, s x ∈ F₁.X ↔ x ∈ F.X) ∧ s F.z - F₁.z ∈ F₁.X
structure Moves (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) (G' G'' : FlagD H r) (β₁ s₁ s₂ : V ≃ₗ[K] V) : Prop where
  base₁ : Carry s₁ F F
  base₂ : Carry s₂ F F
  fst : Carry s₁ F' G'
  snd : Carry s₂ F'' G''
  agree : SameRed F F s₂ s₁
  comm : SameRed F' G'' (β.trans s₂) (s₁.trans β₁)
variable {F F' F'' F₁ G' G'' : FlagD H r} {Λ Λ₁ : Submodule R V} {g : R} {β β₁ s s₁ s₂ : V ≃ₗ[K] V}
namespace RedMap
def mk (β : V ≃ₗ[K] V) (h : IsPairMap F F' F'' Λ g β) : RedMap F F' F'' Λ g := Quot.mk _ ⟨β, h⟩
def out (b : RedMap F F' F'' Λ g) : V ≃ₗ[K] V := (Quot.out b).1
theorem isPairMap (b : RedMap F F' F'' Λ g) : IsPairMap F F' F'' Λ g b.out := (Quot.out b).2
end RedMap
instance (F : FlagD H r) (Λ : Submodule R V) : Nonempty (AutRed F Λ) :=
  ⟨RedMap.mk _ (isPairMap_refl (IsCong.refl F Λ 1))⟩
theorem fixSp_sup_le (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : fixSp F F' F'' β ⊔ F.X ≤ perp H (xPlus F) :=
  sup_le ((fixSp_le _ _ _ _).trans ((wSp_eq F F').le.trans inf_le_left)) (X_le_perp_xPlus F)
variable [FiniteDimensional K V]
theorem corank_add (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) :
    corank F F' F'' β + finrank K ↥(fixSp F F' F'' β ⊔ F.X) = finrank K (perp H (xPlus F)) := by
  rw [corank, ← (Submodule.submoduleOfEquivOfLe (fixSp_sup_le F F' F'' β)).finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _
theorem corank_symm (h : IsPairMap F F' F'' Λ g β) : corank F F'' F' β.symm = corank F F' F'' β := by
  have a := corank_add F F' F'' β
  have b := corank_add F F'' F' β.symm
  rw [h.fixSp_sup_X] at b
  omega
theorem IsScalar.symm (h : IsScalar F F' F'' β) (hp : IsPairMap F F' F'' Λ g β) : IsScalar F F'' F' β.symm := by
  have key {G G₁ : FlagD H r} {A B : FlagD H r} (h1 : IsTransv A G) (h2 : IsTransv B G₁) (t : V ≃ₗ[K] V)
      (h3 : ∀ y ∈ norLift A G, t y ∈ norLift B G₁) (y : V) (hy : t y ∈ norLift B G₁) : y ∈ norLift A G := by
    have : (norLift A G).map (t : V →ₗ[K] V) = norLift B G₁ :=
      Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨y, hy, rfl⟩; exact h3 y hy) (by
        rw [LinearEquiv.finrank_map_eq, (norLift_decomp K V H r _ _ h1).1, (norLift_decomp K V H r _ _ h2).1])
    rw [← this] at hy
    simpa using hy
  refine ⟨h.2.1, h.1, (corank_symm hp).trans h.2.2.1, fun y y' a a' k => ?_⟩
  obtain ⟨y', rfl⟩ := β.surjective y'
  have h1 : y ∈ norLift F F' := key h.1 h.2.1 (LinearEquiv.refl K V) (fun y hy => by
    obtain ⟨b, b', e⟩ := exists_isSig hy (zero_mem _)
    exact (h.2.2.2 _ _ _ _ e).1) y k.1
  have h2 : y' ∈ norLift F' F := key h.1.symm h.2.1.symm β (fun y hy => by
    obtain ⟨b, b', e⟩ := exists_isSig (zero_mem _) hy
    exact (h.2.2.2 _ _ _ _ e).2.1) y' k.2.1
  obtain ⟨b, b', e⟩ := exists_isSig h1 h2
  obtain ⟨rfl, rfl⟩ := (h.2.2.2 _ _ _ _ e).unique h.2.1.disjoint_xPlus k
  simpa using e
omit [FiniteDimensional K V]
namespace Carry
theorem symm (h : Carry s F F₁) : Carry s.symm F₁ F := by
  refine ⟨inv_mem h.1, fun x => by rw [← h.2.1]; simp, ?_⟩
  rw [← h.2.1, map_sub, s.apply_symm_apply, ← neg_sub]
  exact neg_mem h.2.2
end Carry
namespace Moves
variable (h : Moves F F' F'' β G' G'' β₁ s₁ s₂)
include h
end Moves
end GlobalTheory.IntPair
end


