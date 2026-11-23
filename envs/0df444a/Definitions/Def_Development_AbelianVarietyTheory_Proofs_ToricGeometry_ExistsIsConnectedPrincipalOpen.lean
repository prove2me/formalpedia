-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsConnectedPrincipalOpen
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsConnectedPrincipalOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:17.07627+00:00
-- url     : https://prove2.me/theorems/7926349f-5fd6-4bae-af79-213671b40c62
-- title:
--   Exists Is Connected Principal Open
-- statement:
--   Definitions and structural lemmas for Exists Is Connected Principal Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsConnectedPrincipalOpen.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
noncomputable def evalPair {d : ℕ} (z : (Fin d → ℂ) × ℂ) :
    Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ :=
  Polynomial.eval₂RingHom (MvPolynomial.eval z.1) z.2
end GlobalTheory


