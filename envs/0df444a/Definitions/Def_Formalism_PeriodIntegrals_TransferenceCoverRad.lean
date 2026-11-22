-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_TransferenceCoverRad
-- name    : Formalism_PeriodIntegrals_TransferenceCoverRad
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:56.717803+00:00
-- url     : https://prove2.me/theorems/70a71d7c-4968-4e9a-9d06-a6b5639f5814
-- title:
--   Transference Cover Rad
-- statement:
--   Definitions and structural lemmas for Transference Cover Rad, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/TransferenceCoverRad.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace PI
def TransferenceCoverDiv : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (M : Submodule ℤ V), DiscreteTopology M → Submodule.span ℝ (M : Set V) = ⊤ →
    ∀ κ : ℝ, 0 < κ → (∀ y : V, (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → y ≠ 0 → κ ≤ ‖y‖) →
    ∀ x : V, ∃ y ∈ M, ‖x - y‖ ≤ (Module.finrank ℝ V : ℝ) / (2 * κ)
def covRad {N : ℕ} (L : Set (EuclideanSpace ℝ (Fin N))) : ℝ := ⨆ x, Metric.infDist x L
def dualLat {N : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)) :=
  {y | ∀ x ∈ L, ∃ z : ℤ, inner ℝ x y = (z : ℝ)}
def firstMin {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N))) : ℝ :=
  sInf {r | ∃ y ∈ S, y ≠ 0 ∧ r = ‖y‖}
def TransferenceCoverRad : Prop :=
  ∀ (N : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin N))) [DiscreteTopology L], IsZLattice ℝ L →
    covRad (L : Set (EuclideanSpace ℝ (Fin N))) * firstMin (dualLat L) ≤ (N : ℝ) / 2
end PI


