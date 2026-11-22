-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountSt
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:52.681217+00:00
-- url     : https://prove2.me/theorems/8043e6ad-20e8-48d8-a175-409c3256a4a5
-- title:
--   Count St
-- statement:
--   Definitions and structural lemmas for Count St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountSt.lean

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
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
def ZeroDensityBox : Prop :=
  ∃ C : ℝ, ∀ (Q : ℝ) (S : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1))), 3 ≤ Q →
    (∀ p ∈ S, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0) →
    (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts


