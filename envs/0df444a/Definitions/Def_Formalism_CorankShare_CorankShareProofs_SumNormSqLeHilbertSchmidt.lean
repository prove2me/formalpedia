-- Prove2me | Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
-- name    : Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:11:19.071893+00:00
-- url     : https://prove2.me/theorems/f96a3259-b081-4654-b8b6-2ea77fba5a58
-- title:
--   Sum Norm Sq Le Hilbert Schmidt
-- statement:
--   Definitions and structural lemmas for Sum Norm Sq Le Hilbert Schmidt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CorankShareLayerCake.FR
namespace Pgsn2pfrla
open Finset Module LinearMap
open scoped InnerProductSpace
section gen
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
end gen
section fam
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
end fam
section wup
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
end wup
end Pgsn2pfrla
open Finset Module LinearMap Pgsn2pfrla
open scoped InnerProductSpace
end Formalism.CorankShareLayerCake.FR


