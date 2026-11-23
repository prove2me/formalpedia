-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:13.447737+00:00
-- url     : https://prove2.me/theorems/3b251631-898a-4113-853c-163bba1d08ff
-- title:
--   Eff Base
-- statement:
--   Definitions and structural lemmas for Eff Base, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffBase.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.Ext.SupplyAP
def gExp (t : ℝ) : ℝ := 1 / (Real.exp t - 1) - 1 / t
def ExcBoundAt (A : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ),
    χ ^ 2 = 1 → χ ≠ 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 - c * (q : ℝ) ^ (-(A : ℝ))
end Formalism.HermitianLattices.Ext.SupplyAP


