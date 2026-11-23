-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EmbeddingTypeJumps
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EmbeddingTypeJumps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:51.44346+00:00
-- url     : https://prove2.me/theorems/aa591e57-d172-4cc1-9975-57760cb84135
-- title:
--   Embedding Type Jumps
-- statement:
--   Definitions and structural lemmas for Embedding Type Jumps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EmbeddingTypeJumps.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd :
    {E : Type} →
      [inst : Field E] → [inst_1 : NumberField E] → [inst_2 : StarRing E] → (W : Formalism.BasicNotions.HSpace E) → Set (Fin W.rank → E) :=
    fun {E : Type} [Field E] [NumberField E] [StarRing E] (W : Formalism.BasicNotions.HSpace E) ↦
      {x : Fin W.rank → E | ∑ i : Fin W.rank, x i • (W.frame : Fin W.rank → W.V) i ∈ W.L0}


