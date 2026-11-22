-- Prove2me | Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MomentMap
-- name    : BornVolumeLean_LinearAlgebra_Projectivization_MomentMap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:52:06.999583+00:00
-- url     : https://prove2.me/theorems/577c6dc7-b327-4e42-9c91-8be3c1d55c43
-- title:
--   Moment Map
-- statement:
--   Definitions and structural lemmas for Moment Map, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MomentMap.lean

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit false
@[expose] public section
@[expose] public section
open scoped LinearAlgebra.Projectivization
namespace Projectivization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def momentMap (p : ℙ ℂ (EuclideanSpace ℂ ι)) (i : ι) : ℝ :=
  ‖p.rep i‖ ^ 2 / ‖p.rep‖ ^ 2
end Projectivization


