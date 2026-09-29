-- Prove2me | Definitions.Def_mme_dwz_q6_coupled_explicit_grading
-- name    : mme_dwz_q6_coupled_explicit_grading
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T07:19:41.800668+00:00
-- url     : https://prove2.me/theorems/9eaf1f02-8bd3-4417-8b7f-06eacd2bcfe7
-- title:
--   Explicit internal three-grading of the q=6 coupled constituent
-- statement:
--   The q=6 four-sum coupled constituent is graded internally into three coordinate classes. In the first two modes, the two copies of the six-element coordinate family receive grades zero and one. In the third mode, the two exceptional coordinates receive grades zero and one, while the 6 by 6 middle grid receives grade two. The grading is defined by splitting the standard coordinate basis into the spans of these three classes.
-- source:
--   Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, J. Symbolic Computation 9 (1990), coupled four-sum constituent on journal pp. 266 and 270; used for the enhanced 112 analysis in Duan--Wu--Zhou, arXiv:2210.10173v5, Section 6.3. https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_q6_112_coupled_profile_data

open MME Module

namespace MME.DWZComponentRestriction

universe u

set_option autoImplicit false

/-- The source-faithful internal three-grading of the explicit q=6 coupled
four-sum constituent, obtained by splitting its standard coordinate basis. -/
noncomputable def dwzQ6CoupledGrading
    (K : Type u) [Field K] : (coupledObj K 6).TypeGrading 3 where
  decomp s := cwBasisGrade (dwzQ6CoupledBasis K s)
    (dwzQ6CoupledCoordGrade s)
  is_internal s := cwBasisGrade_isInternal
    (dwzQ6CoupledBasis K s) (dwzQ6CoupledCoordGrade s)

end MME.DWZComponentRestriction


