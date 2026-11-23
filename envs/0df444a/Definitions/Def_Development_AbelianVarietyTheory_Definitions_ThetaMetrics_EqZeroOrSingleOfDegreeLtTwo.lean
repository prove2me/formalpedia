-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:57.266741+00:00
-- url     : https://prove2.me/theorems/35c8d0bf-d962-4b20-b9a9-9d23f80187da
-- title:
--   Eq Zero Or Single Of Degree Lt Two
-- statement:
--   Definitions and structural lemmas for Eq Zero Or Single Of Degree Lt Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]
def jacobian (f : τ → MvPowerSeries σ R) : Matrix τ σ R :=
  Matrix.of fun i j => coeff (Finsupp.single j 1) (f i)
def Close (k n : ℕ) (P Q : MvPowerSeries τ S) : Prop :=
  (n : ℕ∞) ≤ P.order ∧ (n : ℕ∞) ≤ Q.order ∧ ((k + n : ℕ) : ℕ∞) ≤ (P - Q).order + 1
variable [Algebra R S]
end FormalSeries
end GlobalTheory


