-- Prove2me | Definitions.Def_TunnellMap_InverseByRerun
-- name    : TunnellMap_InverseByRerun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T16:03:28.899809+00:00
-- url     : https://prove2.me/theorems/ab42f554-1b52-56e2-9c72-ebd94f7d5292
-- title:
--   Inverse By Rerun
-- statement:
--   Definitions and structural lemmas for Inverse By Rerun, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
set_option autoImplicit true
namespace TunnellMap
namespace RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
def HeldGenerated (frames : FrameFamily n) (E : DARun n) : Prop :=
  ∀ v s' r', E.held v = some (s', r') → r' ∈ fullTrace s' (frames s')
section Fin
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
inductive Reaches (frames : FrameFamily n) : DARun n → DARun n → Prop
  | refl (E : DARun n) : Reaches frames E E
  | step {E E' E'' : DARun n} : step frames E = some E' →
      Reaches frames E' E'' → Reaches frames E E''
end Fin
variable [Fintype (BOddRep n)]
noncomputable def inverseByRerun (frames : FrameFamily n)
    (fallback : BResidual n) (y : AResidual n) : BResidual n :=
  ((run frames (DARun.initial (sourceRoster n))).held
      (canonicalTargetLift (residualTargetLift y))).elim fallback
    fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1
section Inverse
variable [Fintype (ARep n)]
end Inverse
end RecordDA
end TunnellMap


