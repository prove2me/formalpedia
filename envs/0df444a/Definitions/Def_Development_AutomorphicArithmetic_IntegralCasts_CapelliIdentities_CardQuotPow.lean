-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardQuotPow
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardQuotPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:07.092069+00:00
-- url     : https://prove2.me/theorems/14c608a5-cea1-4716-9264-8196d0123517
-- title:
--   Card Quot Pow
-- statement:
--   Definitions and structural lemmas for Card Quot Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CardQuotPow.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Yzb5.resQ :
    {F : Type} → [inst : Field F] → [inst_1 : ValuativeRel F] → ↥(ValuativeRel.valuation F).integer → ℕ :=
    fun {F : Type} [Field F] [ValuativeRel F] (ϖ : ↥(ValuativeRel.valuation F).integer) ↦
      Nat.card (↥(ValuativeRel.valuation F).integer ⧸ Ideal.span {ϖ})


