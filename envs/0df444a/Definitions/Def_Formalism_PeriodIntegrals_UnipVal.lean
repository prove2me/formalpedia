-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnipVal
-- name    : Formalism_PeriodIntegrals_UnipVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:06.084863+00:00
-- url     : https://prove2.me/theorems/455f22d7-4e26-473e-bf5f-1e6853e12c28
-- title:
--   Unip Val
-- statement:
--   Definitions and structural lemmas for Unip Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnipVal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace PI.UnipVal
variable {K : Type} [Field K] [NumberField K]
def vw (w : HeightOneSpectrum (𝓞 K)) (a : K) : ℤ :=
  FractionalIdeal.count K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a)
def plc (w : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ w.asIdeal)
def ramw (w : HeightOneSpectrum (𝓞 K)) : ℤ := vw w ((plc w : ℕ) : K)
def UnipVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)),
    (∀ n : ℕ, n ≠ 0 → vw w ((n : ℕ) : K) = ramw w * (padicValNat (plc w) n : ℤ)) ∧
    ∀ g₁ g₂ a : ℕ, g₁.Prime → g₂.Prime → g₁ ≠ g₂ →
      (vw w (((g₁ ^ a * g₂ ^ a : ℕ)) : K) : ℝ) = (ramw w : ℝ) * (if plc w = g₁ ∨ plc w = g₂ then (a : ℝ) else 0)
end PI.UnipVal
end


