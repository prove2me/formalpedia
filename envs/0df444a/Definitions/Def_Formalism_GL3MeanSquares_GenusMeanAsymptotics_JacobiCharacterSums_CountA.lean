-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountA
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:14.651581+00:00
-- url     : https://prove2.me/theorems/7ac1a12a-5b2f-4d5f-89b2-147e69549cfc
-- title:
--   Count A
-- statement:
--   Definitions and structural lemmas for Count A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountA.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
open DirichletCharacter
def toSig {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : Σ N : ℕ, DirichletCharacter ℂ (N + 1) :=
  ⟨n - 1, cast (congrArg (DirichletCharacter ℂ) (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))).symm) χ⟩
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts


