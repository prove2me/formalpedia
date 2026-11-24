-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:15.474545+00:00
-- url     : https://prove2.me/theorems/33e54929-b670-4e15-ae69-b13988f90023
-- title:
--   Zero Locus Dim HGeo
-- statement:
--   Definitions and structural lemmas for Zero Locus Dim HGeo, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open Metric Filter Topology Finset
noncomputable section
namespace ZeroLocusDimH
def paramMap {n r : ℕ} (π : Fin r → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin r → ℂ :=
  fun j => MvPolynomial.eval x (π j)
end ZeroLocusDimH
end
end GroundTheory.Heights₂.Heights


