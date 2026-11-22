-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_WedgeDetNz
-- name    : Formalism_PeriodIntegrals_WedgeDetNz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:09:09.186072+00:00
-- url     : https://prove2.me/theorems/438aa64e-57fe-4166-924d-e9f946f7e3ff
-- title:
--   Wedge Det Nz
-- statement:
--   Definitions and structural lemmas for Wedge Det Nz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/WedgeDetNz.lean

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
def WedgeDetNz : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (ρ : ℕ) (z : Fin ρ → V),
    LinearIndependent K z → ∃ φ : Fin ρ → (V →ₗ[K] K), (Matrix.of fun i k => φ i (z k)).det ≠ 0
end PI


