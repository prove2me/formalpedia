-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZPair
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZPair
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:43:55.153791+00:00
-- url     : https://prove2.me/theorems/c7accf5b-0410-4e81-85ea-8a698c8f7398
-- title:
--   Count ZPair
-- statement:
--   Definitions and structural lemmas for Count ZPair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZPair.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
scoped instance (p p' : PC) : NeZero ((p.1 + 1) * (p'.1 + 1)) := ⟨by positivity⟩
def mulLevel (p p' : PC) : DirichletCharacter ℂ ((p.1 + 1) * (p'.1 + 1)) :=
  DirichletCharacter.changeLevel (dvd_mul_right (p.1 + 1) (p'.1 + 1)) p.2 *
    (DirichletCharacter.changeLevel (dvd_mul_left (p'.1 + 1) (p.1 + 1)) p'.2)⁻¹
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD


