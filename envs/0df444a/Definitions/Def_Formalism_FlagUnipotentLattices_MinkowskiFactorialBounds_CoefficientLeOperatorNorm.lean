-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:11.824414+00:00
-- url     : https://prove2.me/theorems/c6910c3d-c17f-4c76-83a2-f79da694eb2b
-- title:
--   Coefficient Le Operator Norm
-- statement:
--   Definitions and structural lemmas for Coefficient Le Operator Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CoefficientLeOperatorNorm.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
namespace Formalism.HermitianLatticeCounting.P
noncomputable def sfac (k : ℕ) : ℝ := ∏ i ∈ range k, (i.factorial : ℝ)
def IsW (t : ℤ) : Prop := t = 0 ∨ ∃ k : ℕ, t = 4 ^ k ∨ t = -(4 ^ k)
noncomputable def farW (h ε : ℝ) : ℕ → ℝ
  | 0 => 1
  | (k+1) => Real.exp (-(h / 8 * (ε * (2 ^ k * ε))))
noncomputable def farA (B h ε : ℝ) (i : ℕ) : ℝ := Real.exp (B * (2 ^ i * ε)) * farW h ε i
end Formalism.HermitianLatticeCounting.P


