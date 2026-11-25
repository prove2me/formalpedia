-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLenCauchySchwarz
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLenCauchySchwarz
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:37:05.713282+00:00
-- url     : https://prove2.me/theorems/0a748afb-5356-5379-a846-b7cfeb30d110
-- title:
--   St Len Cauchy Schwarz
-- statement:
--   Definitions and structural lemmas for St Len Cauchy Schwarz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StLenCauchySchwarz.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def LenCauchySchwarz.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (g : archUnitary h v) (x y : W) (w : InfinitePlace E),
    ‖w.embedding (h.toSesq x y)‖ ≤ M.len (invApply g (vecAt v x)) * M.len (invApply g (vecAt v y))
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


