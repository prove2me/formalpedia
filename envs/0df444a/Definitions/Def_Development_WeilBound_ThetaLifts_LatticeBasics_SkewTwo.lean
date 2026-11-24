-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_SkewTwo
-- name    : Development_WeilBound_ThetaLifts_LatticeBasics_SkewTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:07.362176+00:00
-- url     : https://prove2.me/theorems/ae908ea8-9f4c-4f08-b7ae-f64fc5b0e7a9
-- title:
--   Skew Two
-- statement:
--   Definitions and structural lemmas for Skew Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/SkewTwo.lean

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThK.Dbl.Vf2
open Matrix GlobalTheory.WeilM PositivityTheory.ThKG.Loc.Cone.Vf
section Skew
variable {A K β : Type} [CommRing A] [Field K] [Fintype β] [DecidableEq β]
variable {c : A →+* A} {r : A →+* K} {G G' M m P Q : Matrix β β A}
end Skew
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] {c : A →ₐ[R] A} [Fintype β] [DecidableEq β] {J : Matrix β β A}
end GlobalTheory.ThK.Dbl.Vf2
end


