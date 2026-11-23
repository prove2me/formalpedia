-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HermitianDiagonalisation
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HermitianDiagonalisation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:01.517369+00:00
-- url     : https://prove2.me/theorems/8e020b31-8a5e-4198-8151-0d07c252932c
-- title:
--   Hermitian Diagonalisation
-- statement:
--   Definitions and structural lemmas for Hermitian Diagonalisation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HermitianDiagonalisation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix in

def Dz {E ι : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι E) : Prop :=
  ∃ g : Matrix ι ι E, g.det ≠ 0 ∧ ∃ D : ι → E, gᴴ * T * g = diagonal D


