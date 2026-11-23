-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOne
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:35.234899+00:00
-- url     : https://prove2.me/theorems/d9d2b443-b0e1-405e-aa7b-78cbda7a9e79
-- title:
--   Additive System Integral Solution Count Of Order One
-- statement:
--   Definitions and structural lemmas for Additive System Integral Solution Count Of Order One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSolutionCountOfOrderOne.lean

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
namespace GlobalTheory.PMonE.LinCount
open Finset GlobalTheory.PMonE
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
def lin (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) : Matrix (Fin (K + 1) × m) (Fin (K + 1) × m) F :=
  fun r c =>
    if r.1 = Fin.last K then
      (if k = 0 then M c.1 r.2 c.2 else if c.1 = Fin.last K then M (k + K) r.2 c.2 else 0)
    else
      (if k = 0 then (if (c.1 : ℕ) = r.1 + 1 ∧ r.2 = c.2 then -1 else 0)
        else if k = 1 then (if r = c then 1 else 0) else 0)
end GlobalTheory.PMonE.LinCount
end


