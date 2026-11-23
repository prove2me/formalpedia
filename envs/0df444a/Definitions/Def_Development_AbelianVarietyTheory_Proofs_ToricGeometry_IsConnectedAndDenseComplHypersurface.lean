-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedAndDenseComplHypersurface
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedAndDenseComplHypersurface
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:52.678733+00:00
-- url     : https://prove2.me/theorems/bb7bed9b-27cc-404c-8941-9c8858bcbb3f
-- title:
--   Is Connected And Dense Compl Hypersurface
-- statement:
--   Definitions and structural lemmas for Is Connected And Dense Compl Hypersurface, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedAndDenseComplHypersurface.lean

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
noncomputable def mvPolynomialOnLine {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ) :
    Polynomial ℂ :=
  MvPolynomial.aeval (fun i => Polynomial.C (a i) + Polynomial.C (b i - a i) * Polynomial.X) q
end GlobalTheory


