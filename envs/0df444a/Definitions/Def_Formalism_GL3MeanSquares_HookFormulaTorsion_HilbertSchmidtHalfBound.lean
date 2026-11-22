-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:10.642457+00:00
-- url     : https://prove2.me/theorems/0e4b5184-f266-4329-88d7-4b00e9eb292f
-- title:
--   Hilbert Schmidt Half Bound
-- statement:
--   Definitions and structural lemmas for Hilbert Schmidt Half Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HilbertSchmidtHalfBound.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
section A
open Finset
end A
section B
open Finset
open scoped ComplexOrder
end B
section C
open Finset MeasureTheory
open scoped ComplexOrder
end C
section D
open Finset
open scoped Nat
end D
section E
open Finset Matrix Unitary
end E
section F
open Finset
def bb (k rS : ℕ) (i : ℕ) : ℕ := if i < rS then i else if i < rS + (k + 1) then rS else i - k
def cc (k rS : ℕ) (j : ℕ) : ℕ := if j < rS then j else if j < rS + (k + 1) then rS else j
end F
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
namespace Formalism.HermitianLattices.CumulantEstimateDefs
end Formalism.HermitianLattices.CumulantEstimateDefs


