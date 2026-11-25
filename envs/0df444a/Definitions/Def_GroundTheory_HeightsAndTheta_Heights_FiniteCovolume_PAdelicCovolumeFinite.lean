-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PAdelicCovolumeFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PAdelicCovolumeFinite
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:42:05.748795+00:00
-- url     : https://prove2.me/theorems/15c8d03f-fdb4-5667-8835-63fbd070bdf4
-- title:
--   PAdelic Covolume Finite
-- statement:
--   Definitions and structural lemmas for PAdelic Covolume Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdelicCovolumeFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdelicLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


