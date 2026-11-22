-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
-- name    : Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:46:03.063325+00:00
-- url     : https://prove2.me/theorems/93186b9e-4a41-4ee9-b95f-836a830406a8
-- title:
--   Exists Sq Abs Norm Of Inert
-- statement:
--   Definitions and structural lemmas for Exists Sq Abs Norm Of Inert, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsSqAbsNormOfInert.lean

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L3
section NoF
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end NoF
section WithF
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
end WithF
end ReciprocityTheory.ChartRestriction.L3


