-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFinsetKerEqBot
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFinsetKerEqBot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:48.443799+00:00
-- url     : https://prove2.me/theorems/c1743f6d-4a1b-4c0d-b508-3970ae1f046c
-- title:
--   Exists Finset Ker Eq Bot
-- statement:
--   Definitions and structural lemmas for Exists Finset Ker Eq Bot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFinsetKerEqBot.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.FinsetKernelTrivial
open scoped BigOperators
noncomputable def restr {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V) (P : Finset X) :
    W →ₗ[ℂ] (P → ℂ) :=
  LinearMap.pi (fun x : P => (LinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) x.1).comp (V.subtype.comp W.subtype))
end GlobalTheory.FinsetKernelTrivial


