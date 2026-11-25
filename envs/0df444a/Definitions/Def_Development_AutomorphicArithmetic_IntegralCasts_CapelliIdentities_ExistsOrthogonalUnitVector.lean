-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsOrthogonalUnitVector
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsOrthogonalUnitVector
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:18.243249+00:00
-- url     : https://prove2.me/theorems/2284a243-d022-5c85-8d54-0ebb69f1fafc
-- title:
--   Exists Orthogonal Unit Vector
-- statement:
--   Definitions and structural lemmas for Exists Orthogonal Unit Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsOrthogonalUnitVector.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.PairUnit :
    {K V : Type} →
      [inst : Field K] →
        [inst_1 : StarRing K] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module K V] → Subring K → (V →ₗ⋆[K] V →ₗ[K] K) → Prop :=
    fun {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [_root_.Module K V] (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) ↦
      ∀ (w y : V),
        ((h : V → V →ₗ[K] K) y : V → K) w = (1 : K) →
          ((h : V → V →ₗ[K] K) w : V → K) w ∈ S →
            ((h : V → V →ₗ[K] K) y : V → K) y ∈ S →
              ∃ c ∈ S,
                ∃ d ∈ S, Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (((h : V → V →ₗ[K] K) (c • w + d • y) : V → K) (c • w + d • y))


