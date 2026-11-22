-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:51.443148+00:00
-- url     : https://prove2.me/theorems/1405b483-500c-4109-8e27-b28905d4e959
-- title:
--   Second Step Gluing
-- statement:
--   Definitions and structural lemmas for Second Step Gluing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
namespace Formalism.DivisionValues
namespace GluingInclusion
open Formalism.HermitianLatticesTheory
section General
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end General
section NF
variable {K : Type} [Field K] [NumberField K]
end NF
section Star
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Star
end GluingInclusion
open GluingInclusion Formalism.HermitianLatticesTheory
end Formalism.DivisionValues


