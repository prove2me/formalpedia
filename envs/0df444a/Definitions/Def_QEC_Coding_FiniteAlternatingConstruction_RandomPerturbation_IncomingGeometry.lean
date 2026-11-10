-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:54:12.086395+00:00
-- url     : https://prove2.me/theorems/e6a6257b-346b-4bb4-90b1-f41fff567f0b
-- title:
--   Incoming Geometry
-- statement:
--   Definitions and structural lemmas for Incoming Geometry, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingGeometry.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Sampling
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
noncomputable def perturbedMap (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (p : Vertex P → Space) : Vertex P → Space :=
  fun v => lambda • ((1/2 : ℝ) • J v)+p v
end QEC.Coding.BDL26RandomPerturbation


