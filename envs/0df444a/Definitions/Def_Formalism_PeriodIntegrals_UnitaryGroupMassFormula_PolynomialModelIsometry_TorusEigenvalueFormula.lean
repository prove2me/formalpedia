-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_TorusEigenvalueFormula
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_TorusEigenvalueFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:27.445836+00:00
-- url     : https://prove2.me/theorems/67b823f3-abef-47e9-8f9c-507373bec575
-- title:
--   Torus Eigenvalue Formula
-- statement:
--   Definitions and structural lemmas for Torus Eigenvalue Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/TorusEigenvalueFormula.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
end PI.WMI


