-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DedekindFactorization_OmegaPoly
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DedekindFactorization_OmegaPoly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:16.733994+00:00
-- url     : https://prove2.me/theorems/1ebe5199-e8fe-4847-9af9-0d491b03fe48
-- title:
--   Omega Poly
-- statement:
--   Definitions and structural lemmas for Omega Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DedekindFactorization/OmegaPoly.lean

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
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open Polynomial
def chiD (d : ℕ) [Fact d.Prime] : DirichletCharacter ℂ d :=
  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
def omegaPoly (d : ℕ) : ℤ[X] := X ^ 2 - X + C (((d + 1) / 4 : ℕ) : ℤ)
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5


