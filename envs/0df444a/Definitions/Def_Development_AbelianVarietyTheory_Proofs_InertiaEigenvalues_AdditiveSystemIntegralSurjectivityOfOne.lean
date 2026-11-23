-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSurjectivityOfOne
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSurjectivityOfOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:00.496032+00:00
-- url     : https://prove2.me/theorems/9cbb6a29-17bc-4c1e-8b02-2358b6867143
-- title:
--   Additive System Integral Surjectivity Of One
-- statement:
--   Definitions and structural lemmas for Additive System Integral Surjectivity Of One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSurjectivityOfOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PMonE
open Finset Matrix
section Lower
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
def lowerOrder (N : ℕ) (M : ℕ → Matrix m m F) (n : ℕ) : Matrix (m ⊕ m) (m ⊕ m) F :=
  fromBlocks (if n = N then 1 else 0) (if n + 1 = N then -1 else 0) (if n = 0 then M 0 else 0) (M (n + 1))
end Lower
end GlobalTheory.PMonE
end


