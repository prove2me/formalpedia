-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T20:40:01.82014+00:00
-- url     : https://prove2.me/theorems/0b5e615c-9ae5-4ebe-9c21-448cccf5d253
-- title:
--   Cm Star Of Is CMUnram
-- statement:
--   Definitions and structural lemmas for Cm Star Of Is CMUnram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CmStarOfIsCMUnram.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__star_isIntegral_8bceb60418dc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
namespace GlobalTheory.SA
open NumberField Module Formalism.BasicNotions
def CMStar (E : Type) [Field E] [StarRing E] : Prop :=
  ∀ (τ : E →+* ℂ) (x : E), τ (star x) = starRingEnd ℂ (τ x)
section AnySpace
variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
def NDLat (h : V →ₗ⋆[E] V →ₗ[E] E) (M : Submodule (𝓞 E) V) : Prop :=
  M.FG ∧ ∀ x ∈ Submodule.span E (M : Set V), (∀ y ∈ M, h y x = 0) → x = 0
def PosOn (h : V →ₗ⋆[E] V →ₗ[E] E) (U : Submodule E V) : Prop :=
  ∀ τ : E →+* ℂ, ∀ x ∈ U, x ≠ 0 → 0 < (τ (h x x)).re
def projAway (h : V →ₗ⋆[E] V →ₗ[E] E) (U : Submodule E V) (M : Submodule (𝓞 E) V) : Submodule (𝓞 E) V :=
  Submodule.span (𝓞 E) {s | (∀ u ∈ U, h u s = 0) ∧ ∃ x ∈ M, x - s ∈ U}
omit [NumberField E] [IsScalarTower (𝓞 E) E V] in

theorem orth_span (h : V →ₗ⋆[E] V →ₗ[E] E) {M : Submodule (𝓞 E) V} {x : V} (hx : ∀ y ∈ M, h y x = 0) :
    ∀ y ∈ Submodule.span E (M : Set V), h y x = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact hx y hy
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
omit [NumberField E] in

theorem ndLat_of_isLattice {h : V →ₗ⋆[E] V →ₗ[E] E} (hn : h.Nondegenerate) {M : Submodule (𝓞 E) V}
    (hM : Submodule.IsLattice E M) : NDLat h M :=
  ⟨hM.fg, fun x _ h0 => hn.2 x fun y => orth_span h h0 y (by rw [hM.span_eq_top]; trivial)⟩
end AnySpace
variable {E : Type} [Field E] [NumberField E] [StarRing E]
structure Amb (S : HSpace E) (k r : ℕ) : Prop where
  cm : CMStar E
  dim : finrank E S.V = k + 2 * r + 1
  neg : ∀ (τ : E →+* ℂ) (U : Submodule E S.V), (∀ x ∈ U, (τ (S.hT x x)).re ≤ 0) → finrank E U ≤ r + 1
abbrev gL {S : HSpace E} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) : Submodule (𝓞 E) S.V :=
  Ideal.span {(g : 𝓞 E)} • Λ
section Diagonal
open Formalism.BasicNotions.Examples₂
def wittSigns (k r : ℕ) : Fin (k + 2 * r + 1) → Bool := fun i => decide ((i : ℕ) < r + 1)
def wittSpace (E : Type) [Field E] [NumberField E] [StarRing E] (k r : ℕ) : HSpace E :=
  stdSpace star_isIntegral (k + 2 * r + 1) (wittSigns k r) (k + r) (r + 1)
example (k r : ℕ) : NDLat (wittSpace E k r).hT (wittSpace E k r).L0 :=
  ndLat_of_isLattice (wittSpace E k r).nondeg (wittSpace E k r).standardTuple_isLattice
end Diagonal
end GlobalTheory.SA
end


