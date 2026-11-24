-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
-- name    : Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:08:44.165033+00:00
-- url     : https://prove2.me/theorems/611ab0fe-7957-42b1-a5dd-a546d5a6e687
-- title:
--   All Positions
-- statement:
--   Definitions and structural lemmas for All Positions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/LatticeFrames/AllPositions.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.SymChain
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
namespace SymData
def SupportAt : Prop :=
  ∀ j c (H : j + c = s) (p : ℕ), 1 ≤ p → p ≤ c → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k,
    h ∈ stabLat ((S.T t).bas (j + 1) c (by omega)) → ∀ x₀ e,
      (S.T t).Phi j c H ((h⁻¹).val * affPt p x₀ e) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) c p, ∃ u ∈ ((S.T t).lev (j + 1) c (by omega)).J, h = r * u
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
def ClassAt : Prop :=
  ∀ j c (H : j + c = s) (p : ℕ), 1 ≤ p → p ≤ c → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k,
    opE S.ψ ν p (om (S.μ (j + 1)) 1 h ((S.T t).Phi j c H)) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) c p, ∃ u ∈ stabLat ((S.T t).bas (j + 1) c (by omega)), h = r * u
def OneIndexAt : Prop :=
  ∀ j c (H : j + c = s) (p : ℕ), 1 ≤ p → p ≤ c → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k,
    opE S.ψ ν p (om (S.μ (j + 1)) 1 h ((S.T t).Phi j c H)) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) c p, ∃ u ∈ ((S.T t).lev (j + 1) c (by omega)).J, h = r * u
def ExchangeAt : Prop :=
  ∀ j c (H : j + c = s) (p : ℕ), 1 ≤ p → p ≤ c → p ≤ S.ρ + 1 → ∃ C : ℝ, 0 < C ∧
    opE S.ψ ν p ((S.T t).Phi j c H) = (C : ℂ) • opE S.ψ ν 1 ((S.T t).Phi j c H)
end SymData
def Average : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ)
    (hμ : ∀ j, IsTame (μ j)) (j : ℕ), ∃ U : Finset (P.iter t μ hμ (j + 1)).J, U.Nonempty ∧
      P.iterPhi t μ hμ j = ∑ u ∈ U, ((P.iter t μ hμ (j + 1)).lam u : ℂ) •
        om (μ (j + 1)) 1 (u : GL (Ix r t (j + 1)) k) ((TypeDatum.principal k r).iterPhi t μ hμ j)
def AllPositions : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneIndexAt t ν ∧ S.ExchangeAt t ν
end GlobalTheory.SymChain


