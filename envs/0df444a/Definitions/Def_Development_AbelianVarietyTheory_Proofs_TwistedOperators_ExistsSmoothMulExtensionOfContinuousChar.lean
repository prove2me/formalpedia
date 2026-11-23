-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:11.464231+00:00
-- url     : https://prove2.me/theorems/3dc2ce6c-a514-4ce5-bb84-a64838ad8b84
-- title:
--   Exists Smooth Mul Extension Of Continuous Char
-- statement:
--   Definitions and structural lemmas for Exists Smooth Mul Extension Of Continuous Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSmoothMulExtensionOfContinuousChar.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
namespace GlobalTheory
noncomputable def mixedExpUnit (K : Type) [Field K] (y : mixedSpace K) : (mixedSpace K)ˣ :=
  ⟨(fun w => Real.exp (y.1 w), fun w => Complex.exp (y.2 w)),
    (fun w => Real.exp (-y.1 w), fun w => Complex.exp (-y.2 w)),
    Prod.ext (funext fun w => by simp [← Real.exp_add])
      (funext fun w => by simp [← Complex.exp_add]),
    Prod.ext (funext fun w => by simp [← Real.exp_add])
      (funext fun w => by simp [← Complex.exp_add])⟩
noncomputable def mixedLog (K : Type) [Field K] (x : mixedSpace K) : mixedSpace K :=
  (fun w => Real.log (x.1 w), fun w => Complex.log (x.2 w))
end GlobalTheory


