-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:22.915815+00:00
-- url     : https://prove2.me/theorems/1091e982-3fb4-4870-b975-6ab7b4a9cd60
-- title:
--   Exists Mul Sub One Mem Pow
-- statement:
--   Definitions and structural lemmas for Exists Mul Sub One Mem Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulSubOneMemPow.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
set_option linter.deprecated false
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.MeanA
variable {R F V : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F] [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
  [FiniteDimensional F V]
end Formalism.HermitianLattices.Ext.L3.MeanA


