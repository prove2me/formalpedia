-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeries__Poulsen_b54a5a55a6942064
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeries__Poulsen_b54a5a55a6942064
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T16:57:12.129993+00:00
-- url     : https://prove2.me/theorems/7d1328cb-2e2e-4ed7-a521-52d22212b43a
-- title:
--   Poulsen
-- statement:
--   Definitions and structural lemmas for Poulsen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/DiscreteSeries₂/Poulsen.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPrAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
noncomputable section
namespace BranchingSupport
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
def IsInvForm {k r : ℕ} (R R' : Rep k r) (Bf : R.H → R'.H → ℂ) : Prop :=
  (∀ x ∈ R.sm, ∀ x' ∈ R.sm, ∀ y ∈ R'.sm, Bf (x + x') y = Bf x y + Bf x' y) ∧
  (∀ (a : ℂ), ∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf (a • x) y = a * Bf x y) ∧
  (∀ x ∈ R.sm, ∀ y ∈ R'.sm, ∀ y' ∈ R'.sm, Bf x (y + y') = Bf x y + Bf x y') ∧
  (∀ (a : ℂ), ∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf x (a • y) = star a * Bf x y) ∧
  (∀ g ∈ GG k r, ∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf (R.σ g x) (R'.σ g y) = Bf x y) ∧
  ∃ (C : ℝ) (Ws Ws' : List (List (Mx k r))), (∀ W ∈ Ws ++ Ws', ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
    ∀ x ∈ R.sm, ∀ y ∈ R'.sm, ‖Bf x y‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W x‖).sum *
      (Ws'.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W y‖).sum
def Poulsen : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r),
    R.IsDS ε mu → R'.IsDS ε mu' →
    (∀ Bf : R.H → R.H → ℂ, IsInvForm R R Bf → ∃ c : ℂ, ∀ x ∈ R.sm, ∀ y ∈ R.sm, Bf x y = c * ⟪y, x⟫_ℂ) ∧
    ∀ Bf : R.H → R'.H → ℂ, IsInvForm R R' Bf → (∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf x y = 0) ∨
      ∃ U : R.H ≃ₗᵢ[ℂ] R'.H, ∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)
end BranchingSupport


