-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_GenModelXi
-- name    : Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_GenModelXi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:25.953522+00:00
-- url     : https://prove2.me/theorems/d6248753-b1c9-4c09-90af-59a562af6642
-- title:
--   Gen Model Xi
-- statement:
--   Definitions and structural lemmas for Gen Model Xi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/GenModelXi.lean

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_GoodLat
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.PairingIndexBounds.Mv
open Formalism.L2.Th1.H
def HeisU : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B : AddSubgroup V), IsHerm H →
    IsSemiChar H A α → IsSemiChar H B α → IsBichar (cU H A B) ∧ IsHeis (cU H A B) (wA H α A) (wB H α B)
def InterSelf : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ : AddSubgroup V), IsHerm H →
    IsSemiChar H Λ α → ∀ θ ∈ fixedBy H α Λ, inter H α Λ Λ θ = θ
def MovesU : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ₀ Λ₁ : AddSubgroup V), IsHerm H →
    IsSemiChar H A α → IsSemiChar H B α → GoodLat H α A B Λ₀ → GoodLat H α A B Λ₁ → relIdx Λ₀ Λ₁ ≠ 0 →
    ∀ θ ∈ fixedBy H α Λ₀, ∀ Xi : Sch (cU H A B) (Λ₀.addSubgroupOf A) →ₗ[ℂ] (V → ℂ),
      IsXi (cU H A B) (wA H α A) (wB H α B) (Λ₀.addSubgroupOf A) θ Xi →
      ∃ h : ind ((Λ₁.addSubgroupOf A : AddSubgroup A) : Set A) ∈ Sch (cU H A B) (Λ₀.addSubgroupOf A),
        0 < volA A Λ₀ Λ₁ ∧
        inter H α Λ₀ Λ₁ θ = (((Real.sqrt (volA A Λ₀ Λ₁))⁻¹ : ℝ) : ℂ) • Xi ⟨_, h⟩
def MovesComposeU : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ₀ Λ₁ Λ₂ : AddSubgroup V), IsHerm H →
    IsSemiChar H A α → IsSemiChar H B α → GoodLat H α A B Λ₀ → GoodLat H α A B Λ₁ → GoodLat H α A B Λ₂ →
    relIdx Λ₀ Λ₁ ≠ 0 → relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₀ Λ₂ ≠ 0 →
    ∀ θ ∈ fixedBy H α Λ₀, inter H α Λ₁ Λ₂ (inter H α Λ₀ Λ₁ θ) = inter H α Λ₀ Λ₂ θ
def GenModelXi : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₀ : AddSubgroup V) (M ι : Type)
    (Λ : ι → AddSubgroup V) (Y : ι → Set M) (vol : ι → ℝ), IsHerm H →
    ∀ θ ∈ fixedBy H α Λ₀,
    (∀ s : Finset ι, ∃ (A B : AddSubgroup V) (φ : A → M), IsSemiChar H A α ∧ IsSemiChar H B α ∧
      GoodLat H α A B Λ₀ ∧ ∀ i ∈ s, GoodLat H α A B (Λ i) ∧ relIdx Λ₀ (Λ i) ≠ 0 ∧
        (∀ a : A, (a : V) ∈ Λ i ↔ φ a ∈ Y i) ∧ vol i = volA A Λ₀ (Λ i)) →
    ∃ Xi : (M → ℂ) →ₗ[ℂ] (V → ℂ), ∀ i, Xi (Set.indicator (Y i) 1) = ((Real.sqrt (vol i) : ℝ) : ℂ) • inter H α Λ₀ (Λ i) θ
end Formalism.L2.PairingIndexBounds.Mv


