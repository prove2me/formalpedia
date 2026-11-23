-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardinalityOfBand
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardinalityOfBand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:22.277448+00:00
-- url     : https://prove2.me/theorems/1a416299-520d-40ee-be43-6f5fd5e9407f
-- title:
--   Cardinality Of Band
-- statement:
--   Definitions and structural lemmas for Cardinality Of Band, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CardinalityOfBand.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.CardinalityOfBand.band :
    (m : Nat) → Nat → Nat → Fin m → Bool :=
    fun (m a b : Nat) (i : Fin m) ↦
      @Decidable.decide (And (@LE.le Nat instLENat a (@Fin.val m i)) (@LT.lt Nat instLTNat (@Fin.val m i) b))
        (@instDecidableAnd (@LE.le Nat instLENat a (@Fin.val m i)) (@LT.lt Nat instLTNat (@Fin.val m i) b)
          (a.decLe (@Fin.val m i)) ((@Fin.val m i).decLt b))


