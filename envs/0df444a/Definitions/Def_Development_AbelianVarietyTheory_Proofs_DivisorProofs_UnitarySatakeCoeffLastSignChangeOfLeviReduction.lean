-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffLastSignChangeOfLeviReduction
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffLastSignChangeOfLeviReduction
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:10:58.226071+00:00
-- url     : https://prove2.me/theorems/a68aa0c1-6d58-4a4e-91cc-98777bad2f25
-- title:
--   Unitary Satake Coeff Last Sign Change Of Levi Reduction
-- statement:
--   Definitions and structural lemmas for Unitary Satake Coeff Last Sign Change Of Levi Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitarySatakeCoeffLastSignChangeOfLeviReduction.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl.Neg
def ext {m : ℕ} (a : Fin m → ℤ) (x : ℕ) : ℤ := if h : x < m then a ⟨x, h⟩ else 0
def expo (n m : ℕ) (A : ℕ → ℤ) (x : Fin n) : ℤ :=
  if x.val < m then A x else if n - m ≤ x.val then -A (n - 1 - x.val) else 0
def mid {n : ℕ} (k r : ℕ) (h : n = 2 * k + r) (j : Fin r) : Fin n := ⟨k + j.val, by have := j.2; omega⟩
end GlobalTheory.SatakeWeyl.Neg
end


