-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_PsiAPLeCount
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_PsiAPLeCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:17.112667+00:00
-- url     : https://prove2.me/theorems/4e17e2aa-02a3-440d-a0ab-c5a16916f02d
-- title:
--   Psi APLe Count
-- statement:
--   Definitions and structural lemmas for Psi APLe Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/PsiAPLeCount.lean

import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
namespace Formalism.HermitianLattices.Ext.SupplyAP
def primesAP (m a : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])
end Formalism.HermitianLattices.Ext.SupplyAP


