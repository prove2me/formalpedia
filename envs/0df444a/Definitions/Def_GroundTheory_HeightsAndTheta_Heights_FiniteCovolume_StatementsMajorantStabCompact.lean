-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsMajorantStabCompact
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsMajorantStabCompact
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:46:45.356129+00:00
-- url     : https://prove2.me/theorems/b07852dd-34cc-58fa-bbfd-949b938ef40c
-- title:
--   Statements Majorant Stab Compact
-- statement:
--   Definitions and structural lemmas for Statements Majorant Stab Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsMajorantStabCompact.lean

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
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def MajorantStabCompact.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ M : Majorant h v, IsCompact (M.stab : Set (archUnitary h v))
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


