-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
-- name    : Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:51.050772+00:00
-- url     : https://prove2.me/theorems/1d039d8b-3c92-4a04-bf24-e25f65756709
-- title:
--   Op Norm At Le Of Points
-- statement:
--   Definitions and structural lemmas for Op Norm At Le Of Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
namespace Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
namespace BlockMetrics
section Forms
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)
def fcA : V →+ (ι → ℂ) :=
  AddMonoidHom.mk' (Formalism.HermitianLatticesTheory.fcoord b X v) (Formalism.HermitianLatticesTheory.fcoord_add b X v)
end Forms
end BlockMetrics
open BlockMetrics
end Formalism.IndefR.LatticeTransfer


