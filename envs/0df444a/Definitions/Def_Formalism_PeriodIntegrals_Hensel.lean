-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_Hensel
-- name    : Formalism_PeriodIntegrals_Hensel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:16.506799+00:00
-- url     : https://prove2.me/theorems/33636a35-d382-4532-806d-a012cb6f5d11
-- title:
--   Hensel
-- statement:
--   Definitions and structural lemmas for Hensel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/Hensel.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
namespace PI
def HenselStrong : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (f : Polynomial 𝒪[F]) (a : 𝒪[F]),
    valuation F ((f.eval a : 𝒪[F]) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F) ^ 2 →
    ∃ b : 𝒪[F], f.eval b = 0 ∧
      valuation F (((b - a : 𝒪[F])) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F)
end PI


