-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
-- name    : Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:34.513778+00:00
-- url     : https://prove2.me/theorems/33ca5254-1941-4ab0-9496-d508795c50ae
-- title:
--   Fin Norm Surj
-- statement:
--   Definitions and structural lemmas for Fin Norm Surj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/FinNormSurj.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.IndefR.LocBrg
def FinNormSurj : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (τ : k →+* k), (∀ x, τ (τ x) = x) → (∃ x, τ x ≠ x) →
    ∀ c : k, τ c = c → c ≠ 0 → ∃ x : k, τ x * x = c
def HenselSqrt : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L],
    Valued.v (2 : L) = 1 → ∀ u : L, Valued.v (u - 1) < 1 → ∃ s : L, s * s = u ∧ Valued.v (s - 1) < 1
end Formalism.IndefR.LocBrg


