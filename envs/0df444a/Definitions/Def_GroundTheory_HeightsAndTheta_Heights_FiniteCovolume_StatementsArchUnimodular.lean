-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsArchUnimodular
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsArchUnimodular
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:45:33.225799+00:00
-- url     : https://prove2.me/theorems/f03d086b-decf-5a04-92c0-4e4693884b26
-- title:
--   Statements Arch Unimodular
-- statement:
--   Definitions and structural lemmas for Statements Arch Unimodular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsArchUnimodular.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVecFixGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def ArchUnimodular.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure], μ.IsMulRightInvariant
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


