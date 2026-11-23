-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:09.767214+00:00
-- url     : https://prove2.me/theorems/ccf26d4a-1ef8-4882-98a9-879320aa199b
-- title:
--   Line Transport
-- statement:
--   Definitions and structural lemmas for Line Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/LineTransport.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
def InterClass : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ₂ α → ∀ F ∈ fixedBy H α Λ₁, ∀ x ∈ Λ₂, ∀ y ∈ Λ₂, y ∈ Λ₁ → ∀ z,
      α (x + y) * opU H (x + y) F z = α x * opU H x F z
def RepsExist : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Λ₁ Λ₂ : AddSubgroup V), relIdx Λ₁ Λ₂ ≠ 0 →
    (∃ S : Finset V, IsReps Λ₁ Λ₂ S) ∧ ∀ S : Finset V, IsReps Λ₁ Λ₂ S → S.card = relIdx Λ₁ Λ₂
def InterReps : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ₂ α → ∀ F ∈ fixedBy H α Λ₁, ∀ S : Finset V, IsReps Λ₁ Λ₂ S → ∀ z,
      inter H α Λ₁ Λ₂ F z = ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ * sumU H α S F z
def InterFixed : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ₂ α → relIdx Λ₁ Λ₂ ≠ 0 → ∀ F ∈ fixedBy H α Λ₁, inter H α Λ₁ Λ₂ F ∈ fixedBy H α Λ₂
def InterTh : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsHerm H →
    ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ), IsSemiChar H Λ₂ α → relIdx Λ₁ Λ₂ ≠ 0 →
      ∀ F ∈ Th H α Λ₁, inter H α Λ₁ Λ₂ F ∈ Th H α Λ₂
def IndexEq : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V),
    IsSelfDual H Λ₁ → IsSelfDual H Λ₂ → relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₂ Λ₁ ≠ 0 → relIdx Λ₁ Λ₂ = relIdx Λ₂ Λ₁
def CharSum : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V),
    IsSelfDual H Λ₁ → IsSelfDual H Λ₂ → ∀ S : Finset V, IsReps Λ₂ Λ₁ S → ∀ y ∈ Λ₂,
      ∑ x ∈ S, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ))
        = by classical exact if y ∈ Λ₁ then (S.card : ℂ) else 0
def InterInv : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSelfDual H Λ₁ → IsSelfDual H Λ₂ → IsSemiChar H Λ₁ α → IsSemiChar H Λ₂ α →
    relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₂ Λ₁ ≠ 0 → ∀ F ∈ fixedBy H α Λ₁, ∀ z,
      inter H α Λ₂ Λ₁ (inter H α Λ₁ Λ₂ F) z = F z
def LineTransport : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsHerm H →
    ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSelfDual H Λ₁ → IsSelfDual H Λ₂ → IsSemiChar H Λ₁ α → IsSemiChar H Λ₂ α →
    relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₂ Λ₁ ≠ 0 → ∀ θ₁ ∈ Th H α Λ₁, θ₁ ≠ 0 → (∀ F ∈ Th H α Λ₁, ∃ c : ℂ, F = c • θ₁) →
      inter H α Λ₁ Λ₂ θ₁ ≠ 0 ∧ ∀ F ∈ Th H α Λ₂, ∃ c : ℂ, F = c • inter H α Λ₁ Λ₂ θ₁
def ThIsom : Prop :=
  ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] [FiniteDimensional ℂ W] (H : Sesq V) (H' : Sesq W) (g : V ≃ₗ[ℂ] W),
    IsIsom H H' (g : V →ₗ[ℂ] W) → ∀ (Λ : AddSubgroup V) (α' : W → ℂ) (G : W → ℂ),
      G ∈ Th H' α' (imgLat (g : V →ₗ[ℂ] W) Λ) ↔ (fun v => G (g v)) ∈ Th H (fun v => α' (g v)) Λ
end Formalism.L2.Th1.H


