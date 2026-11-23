-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LatDefs
-- name    : Formalism_PeriodIntegrals_LatDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:16.053561+00:00
-- url     : https://prove2.me/theorems/6fe2ec31-65e4-4a79-9704-22f3b3a12b0d
-- title:
--   Lat Defs
-- statement:
--   Definitions and structural lemmas for Lat Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LatDefs.lean

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
namespace PI
def lat2 (w₁ w₂ : ℂ) : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂}
def area (Λ : AddSubgroup ℂ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, a = |((starRingEnd ℂ) w₁ * w₂).im|}
def U1 (Λ : AddSubgroup ℂ) (ω : ℂ) (G : ℂ → ℂ) : ℂ → ℂ :=
  fun z => G (z + ω) * Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) -
    (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ)))
def eisG (Λ : AddSubgroup ℂ) (k : ℕ) : ℂ :=
  ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)
def g2 (Λ : AddSubgroup ℂ) : ℂ := 60 * eisG Λ 2
def g3 (Λ : AddSubgroup ℂ) : ℂ := 140 * eisG Λ 3
def discr (Λ : AddSubgroup ℂ) : ℂ := g2 Λ ^ 3 - 27 * g3 Λ ^ 2
end PI
end


