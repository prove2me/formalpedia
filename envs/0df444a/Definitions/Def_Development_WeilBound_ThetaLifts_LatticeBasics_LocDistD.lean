-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
-- name    : Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:23.88981+00:00
-- url     : https://prove2.me/theorems/4bc417ff-6e0b-46d2-b381-0a987d5bf70d
-- title:
--   Loc Dist D
-- statement:
--   Definitions and structural lemmas for Loc Dist D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistD.lean

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
namespace GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]
  [NonarchimedeanAddGroup k] [LocallyCompactSpace k] {c : k → ℂ} {ϖ : k}
def Claim (c : k → ℂ) (n d : ℕ) : Prop :=
  ∀ l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ, Eqv c l → (∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) → ∀ φ ∈ SB _, l φ = 0
end GlobalTheory.ThK.Dbl.LD


