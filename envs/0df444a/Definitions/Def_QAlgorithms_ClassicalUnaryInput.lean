-- Prove2me | Definitions.Def_QAlgorithms_ClassicalUnaryInput
-- name    : QAlgorithms_ClassicalUnaryInput
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:40:00.97598+00:00
-- url     : https://prove2.me/theorems/2675d511-d4ea-4377-8dc7-39d451bdb094
-- title:
--   Unary input for a natural size parameter
-- statement:
--   The unary word for a natural number n is the binary string containing exactly n true bits. For n=0 it is the empty string. This is the unchanged reviewed input convention for polynomial-time uniform circuit generators.
-- source:
--   Reviewed QAlgorithms.Complexity.unary, the size-input convention used in the NLTS circuit-family statements from arXiv:2206.13228v4.

import Definitions.Def_QAlgorithms_ClassicalStringComputability

namespace QAlgorithms.Complexity

/-- Copied from `ShiBQP.unary`: the unary encoding `1^n`. -/
def unary (n : ℕ) : Str := List.replicate n true

end QAlgorithms.Complexity


