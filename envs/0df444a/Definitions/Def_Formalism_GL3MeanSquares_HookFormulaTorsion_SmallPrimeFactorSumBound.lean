-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:38.717783+00:00
-- url     : https://prove2.me/theorems/a45cc60b-b041-4f94-bcf6-aa4b43b6ca94
-- title:
--   Small Prime Factor Sum Bound
-- statement:
--   Definitions and structural lemmas for Small Prime Factor Sum Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SmallPrimeFactorSumBound.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
namespace Formalism.HermitianLattices.GL2PrimeSums
def primesLeFinset (N : ℕ) : Finset ℕ := (Icc 1 N).filter IsPrimePow
noncomputable def primeTermWeight (x : ℝ) (N p : ℕ) : ℝ := ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac = p), cn x n
end Formalism.HermitianLattices.GL2PrimeSums


