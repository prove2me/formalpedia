-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerRest
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerRest
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:13.921813+00:00
-- url     : https://prove2.me/theorems/f9943dc0-a535-48ed-8f22-eb7fafe3fad4
-- title:
--   Imports Ter Rest
-- statement:
--   Definitions and structural lemmas for Imports Ter Rest, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsTerRest.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qe31.Statement :
    Prop :=
    ∀ (T : Type) [inst : CommRing T] [IsNoetherianRing T] (P : Ideal T) [inst_2 : P.IsPrime] (h : ℕ) (f : Fin h → T),
      (∀ (i : Fin h), f i ∈ P) →
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤
            Ideal.span
                (Set.range fun (i : Fin h) ↦
                  (Algebra.algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) ⊔
              IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ (2 : ℕ) →
          ∃ s ∉ P, ∀ x ∈ P, s * x ∈ Ideal.span (Set.range f)


