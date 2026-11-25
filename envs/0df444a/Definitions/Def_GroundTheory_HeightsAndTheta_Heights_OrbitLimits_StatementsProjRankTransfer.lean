-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRankTransfer
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRankTransfer
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T13:05:35.136801+00:00
-- url     : https://prove2.me/theorems/f313c02a-ba81-5124-aa4b-e5c6cabd8828
-- title:
--   Statements Proj Rank Transfer
-- statement:
--   Definitions and structural lemmas for Statements Proj Rank Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsProjRankTransfer.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjMaxRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
def ProjRankTransfer.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsClosed V → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ x ∈ projFullRank R BV, ∃ y ∈ connectedComponent x, y ∈ projMaxRank R Ψ BV
end GroundTheory.Heights₂.Heights.Targets


