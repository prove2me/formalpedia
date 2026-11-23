-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:48.701175+00:00
-- url     : https://prove2.me/theorems/2ba3a9e2-cd4f-4e17-b8d9-4cdbd8765398
-- title:
--   Bijective Algebra Map Integral Closure Of Birational
-- statement:
--   Definitions and structural lemmas for Bijective Algebra Map Integral Closure Of Birational, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
namespace GlobalTheory
universe u
section Normal
variable {X Y : Scheme.{u}}
end Normal
section Constructible
end Constructible
section Etale
variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
end Etale
end GlobalTheory


