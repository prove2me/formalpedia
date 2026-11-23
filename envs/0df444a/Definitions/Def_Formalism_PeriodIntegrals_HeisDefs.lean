-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_HeisDefs
-- name    : Formalism_PeriodIntegrals_HeisDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:24.933293+00:00
-- url     : https://prove2.me/theorems/a1e58618-1d6c-4f24-bba6-c66e3c9c4e4d
-- title:
--   Heis Defs
-- statement:
--   Definitions and structural lemmas for Heis Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HeisDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
section Heis
variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]
noncomputable def HfG (A : ℝ) (z w : T → I → J → ℂ) : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (A : ℂ)
noncomputable def UG (A : ℝ) (x : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ) : (T → I → J → ℂ) → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * HfG A z x - (Real.pi : ℂ) * HfG A x x / 2)
end Heis
end PI


