-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TpCoeffNorm
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TpCoeffNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:52.016584+00:00
-- url     : https://prove2.me/theorems/8877deae-cc4f-46b3-afe5-e1c05c8586b4
-- title:
--   Tp Coeff Norm
-- statement:
--   Definitions and structural lemmas for Tp Coeff Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TpCoeffNorm.lean

import Mathlib
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
def tp (n : ℕ) (z : Fin n → ℂ) : ℂ[X] := ∏ i, (X - C (z i))
end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2


