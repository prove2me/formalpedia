-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StagedEstimateHolds
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StagedEstimateHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:04.939959+00:00
-- url     : https://prove2.me/theorems/7386a3e6-99d1-4313-a286-6111741d43dd
-- title:
--   Staged Estimate Holds
-- statement:
--   Definitions and structural lemmas for Staged Estimate Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StagedEstimateHolds.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {G : Type} [Group G] {P Δ Γ : Subgroup G}
def cls (y : Γ) : Cos P Γ := Quotient.mk _ y
theorem rep_mem (q : Cos P Γ) : rep q ∈ Γ := (Quotient.out q).2
noncomputable def glue (hΔ : Δ ≤ Γ) (s : (_ : Cos Δ Γ) × Cos P Δ) : Cos P Γ :=
  cls ⟨rep s.2 * rep s.1, Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _)⟩
end GlobalTheory.CompanionTheory.RgEis


