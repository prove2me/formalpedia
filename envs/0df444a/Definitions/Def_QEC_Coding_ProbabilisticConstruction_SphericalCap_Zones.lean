-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
-- name    : QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:07:58.673119+00:00
-- url     : https://prove2.me/theorems/e9fef37e-235a-478e-84f1-751812ed1f75
-- title:
--   Zones
-- statement:
--   Definitions and structural lemmas for Zones, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Zones.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal
noncomputable def capHeight (c : ℝ) : ℝ := max 0 (1-max (-1) c)
def zone (u : Sphere) (a b : ℝ) : Set Sphere :=
  {s | a ≤ inner ℝ (u : Space) (s : Space) ∧ inner ℝ (u : Space) (s : Space) ≤ b}
end QEC.Coding.ProbabilisticConstruction.SphericalCap


