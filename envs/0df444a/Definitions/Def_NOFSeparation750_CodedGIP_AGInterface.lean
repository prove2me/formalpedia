-- Prove2me | Definitions.Def_NOFSeparation750_CodedGIP_AGInterface
-- name    : NOFSeparation750_CodedGIP_AGInterface
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:53:16.52964+00:00
-- url     : https://prove2.me/theorems/4689f33a-bf7f-4cad-bdf7-2dd3090319f0
-- title:
--   Algebraic-geometry evaluation-code interface
-- statement:
--   This import-only interface makes the platform's proved algebraic-geometry evaluation-code results available through one short module name. It exposes evaluation codes, their Riemann–Roch dimension bounds, the designed-distance bound, and containment of binary star products. These are the generic ingredients needed for the one-point AG-code argument in Appendix A of the source paper; no new mathematical object or axiom is introduced.
-- source:
--   Wang–Wang–Wu, STOC 2027 submission #750, Appendix A.1 and A.3, pp.11–13; Lean-QECert algebraic-geometry evaluation-code API, https://github.com/QudeLeap/Lean-QECert/tree/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes

import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_distance_lower_bound
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_dimension_lower_bound
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_dimension_eq_of_large_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_starProduct_le_agEvaluationCode_add


