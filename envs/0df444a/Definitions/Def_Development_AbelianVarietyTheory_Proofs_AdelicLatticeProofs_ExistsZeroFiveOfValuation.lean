-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:23.650139+00:00
-- url     : https://prove2.me/theorems/6f46c495-3026-415f-b9ea-9134b10588f1
-- title:
--   Exists Zero Five Of Valuation
-- statement:
--   Definitions and structural lemmas for Exists Zero Five Of Valuation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
namespace GlobalTheory.LocalQuad
namespace FiveVar
variable {K : Type*} [Field K] {n : Type*} [Fintype n]
def qf (a x : n → K) : K := ∑ i, a i * x i ^ 2
def bf (a x y : n → K) : K := ∑ i, 2 * a i * x i * y i
variable [DecidableEq n]
end FiveVar
end GlobalTheory.LocalQuad


