-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:40.345425+00:00
-- url     : https://prove2.me/theorems/6a95bcdd-86b9-4e48-9534-9f01d57a602d
-- title:
--   Formal Degree From Orthogonality
-- statement:
--   Definitions and structural lemmas for Formal Degree From Orthogonality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/FormalDegreeFromOrthogonality.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_HCFdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.HCFdeg
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace
def Irr {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : G →* (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤
def StSchur : Prop :=
  ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : G →* (H →L[ℂ] H)),
    (∀ g v, ‖π g v‖ = ‖v‖) → Irr π → ∀ T : H →L[ℂ] H, (∀ g, T ∘L π g = π g ∘L T) →
    ∃ c : ℂ, T = c • ContinuousLinearMap.id ℂ H
def StBdd : Prop :=
  ∀ (X H : Type) [MeasurableSpace X] (μ : Measure X) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (c : H →ₗ[ℂ] (X → ℂ)), (∀ x, Continuous fun v => c v x) → (∀ v, MemLp (c v) 2 μ) →
    ∃ T : H →L[ℂ] Lp ℂ 2 μ, ∀ v, (T v : X → ℂ) =ᵐ[μ] c v
def StOrth : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (π : G →* (H →L[ℂ] H)),
    (∀ g v, ‖π g v‖ = ‖v‖) → (∀ v, Continuous fun g => π g v) → Irr π →
    (∀ v w : H, MemLp (fun g => ⟪w, π g v⟫_ℂ) 2 μ) →
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun g => ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ) μ ∧
      ∫ g, ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)
def StOrthOf : Prop := StSchur → StBdd → StOrth
def StUnimod : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), (muG ε).IsMulRightInvariant ∧ (muG ε).IsInvInvariant
def StableSubspaceMobius : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsSqIntOn ε σ →
    ∃ d : ℝ, IsFdeg (muG ε) σ d
def FormalDegreeFromOrthogonality : Prop := StOrth → StUnimod → StableSubspaceMobius
def FormalDegreeValue : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
      ∀ d : ℝ, IsFdeg (muG ε) σ d → d = c * fdegHC lam
end PIW.HCFdeg


