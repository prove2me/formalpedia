-- Prove2me | Definitions.Def_NOFSeparation750_CodedGIP_AGCore
-- name    : NOFSeparation750_CodedGIP_AGCore
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:58:38.773313+00:00
-- url     : https://prove2.me/theorems/baacda26-27ea-4be4-98b1-ade1c8fafb97
-- title:
--   Core AG evaluation-code bounds
-- statement:
--   This import-only interface exposes the proved generic evaluation-code dimension lower bound, designed-distance bound, and binary star-product containment through a short module name. It supplies the generic coding facts used in Appendix A.3 of the source paper without introducing any new definition or assumption.
-- source:
--   Wang–Wang–Wu, STOC 2027 submission #750, Appendix A.3, pp.12–13; Lean-QECert evaluation-code API, https://github.com/QudeLeap/Lean-QECert/tree/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes

import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_distance_lower_bound
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_dimension_lower_bound
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_starProduct_le_agEvaluationCode_add


