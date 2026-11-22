-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_HDSucc
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_HDSucc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:39.114907+00:00
-- url     : https://prove2.me/theorems/1fa80454-ce25-4446-b37d-494fc2dc8f50
-- title:
--   HDSucc
-- statement:
--   Definitions and structural lemmas for HDSucc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/HDSucc.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TpCoeffNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Polynomial
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
def hD (φ : ℕ → ℂ) (x : ℂ) (b : ℕ) : ℂ := ∑ a ∈ range (b + 1), φ a * x ^ (b - a)
end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2


