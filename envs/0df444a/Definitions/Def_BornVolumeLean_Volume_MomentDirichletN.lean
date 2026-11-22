-- Prove2me | Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
-- name    : BornVolumeLean_Volume_MomentDirichletN
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:02:41.161782+00:00
-- url     : https://prove2.me/theorems/336c876f-e50d-4db0-ba81-6b8981d59d2b
-- title:
--   Moment Dirichlet N
-- statement:
--   Definitions and structural lemmas for Moment Dirichlet N, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentDirichletN.lean

module
public import Definitions.Def_BornVolumeLean_Volume_GaussianCPN
public import Definitions.Def_BornVolumeLean_Volume_MomentMap
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN
public import Definitions.Def_BornVolumeLean_Volume_MomentBridgeN
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory ProbabilityTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
namespace BornVolume
variable {M : ℕ}
end BornVolume


