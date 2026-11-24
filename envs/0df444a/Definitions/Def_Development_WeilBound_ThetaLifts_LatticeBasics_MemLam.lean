-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_MemLam
-- name    : Development_WeilBound_ThetaLifts_LatticeBasics_MemLam
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:48.392931+00:00
-- url     : https://prove2.me/theorems/937b2cb6-e8b5-4e03-b037-54cd9f45405d
-- title:
--   Mem Lam
-- statement:
--   Definitions and structural lemmas for Mem Lam, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/MemLam.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThK.Dbl.Bmp
open Matrix
variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
variable (K) in

def lam (a : O) (m m' : ℕ) : Submodule O (Matrix (Fin m) (Fin m') K) :=
  LinearMap.range (a • (Algebra.linearMap O K).mapMatrix)
variable {a : O} {n d : ℕ}
end GlobalTheory.ThK.Dbl.Bmp
end


