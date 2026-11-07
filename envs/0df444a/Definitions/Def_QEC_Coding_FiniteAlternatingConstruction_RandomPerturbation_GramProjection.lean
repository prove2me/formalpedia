-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:08:58.791925+00:00
-- url     : https://prove2.me/theorems/f9d068df-944b-418a-b9d1-f38f535f3aac
-- title:
--   Gram Projection
-- statement:
--   Definitions and structural lemmas for Gram Projection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GramProjection.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
noncomputable def gramDet (b c : Space) : ℝ := ‖b‖^2*‖c‖^2-(inner ℝ b c)^2
noncomputable def planeU (b c d : Space) : ℝ :=
  (‖c‖^2*inner ℝ d b-inner ℝ b c*inner ℝ d c)/gramDet b c
noncomputable def planeV (b c d : Space) : ℝ :=
  (‖b‖^2*inner ℝ d c-inner ℝ b c*inner ℝ d b)/gramDet b c
end QEC.Coding.BDL26RandomPerturbation


