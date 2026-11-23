-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt
-- name    : ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:29.339924+00:00
-- url     : https://prove2.me/theorems/5c4d9c64-20ef-4591-b573-5ef2e4328742
-- title:
--   Gram St
-- statement:
--   Definitions and structural lemmas for Gram St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.GeometryOfNumbersTheory
open Matrix
open scoped ComplexOrder MatrixOrder
section SlopeTestRemainingChoices
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end SlopeTestRemainingChoices
section Block
variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
end Block
end ReciprocityTheory.GeometryOfNumbersTheory


