-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AbsoluteConvergence_CayleyMulConjTranspose
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AbsoluteConvergence_CayleyMulConjTranspose
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:48.710041+00:00
-- url     : https://prove2.me/theorems/e34dd923-c5ed-4ced-8e19-78ce63c68666
-- title:
--   Cayley Mul Conj Transpose
-- statement:
--   Definitions and structural lemmas for Cayley Mul Conj Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AbsoluteConvergence/CayleyMulConjTranspose.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_IsSingTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open Matrix
noncomputable section
namespace PositivityTheory.Rg.Sw.KAKB
open PositivityTheory.Rg.Sw
variable {n : ℕ}
def S0 (n : ℕ) : M2 n := fromBlocks 1 0 0 (-1)
def C0 (n : ℕ) : M2 n := fromBlocks 1 1 (Complex.I • 1) (-(Complex.I • 1))
def C1 (n : ℕ) : M2 n := (1 / 2 : ℂ) • (C0 n)ᴴ
end PositivityTheory.Rg.Sw.KAKB
end


