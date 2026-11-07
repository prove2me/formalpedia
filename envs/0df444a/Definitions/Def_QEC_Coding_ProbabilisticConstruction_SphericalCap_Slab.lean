-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
-- name    : QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:08:32.789296+00:00
-- url     : https://prove2.me/theorems/9e8378d6-f522-426a-a756-207a273c887c
-- title:
--   Slab
-- statement:
--   Definitions and structural lemmas for Slab, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Slab.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal
def slab (n : Sphere) (d h : ℝ) : Set Space :=
  {p | |inner ℝ (n : Space) p - d| ≤ h}
end QEC.Coding.ProbabilisticConstruction.SphericalCap


