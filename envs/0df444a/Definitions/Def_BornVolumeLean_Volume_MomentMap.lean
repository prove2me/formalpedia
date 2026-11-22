-- Prove2me | Definitions.Def_BornVolumeLean_Volume_MomentMap
-- name    : BornVolumeLean_Volume_MomentMap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:57:48.924329+00:00
-- url     : https://prove2.me/theorems/6af7aba9-55ab-461c-a173-87da8a9f251e
-- title:
--   Moment Map
-- statement:
--   Definitions and structural lemmas for Moment Map, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentMap.lean

module
public import Definitions.Def_BornVolumeLean_Volume_CPN
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MomentMap
public import Theorems.Thm_Projectivization_momentMap_mk
public import Theorems.Thm_Projectivization_momentMap_mk_eq_inner_sq
public import Theorems.Thm_Projectivization_momentMap_sum_eq_one
public import Theorems.Thm_Projectivization_momentRatio_smul

set_option autoImplicit false
@[expose] public section
@[expose] public section
open scoped LinearAlgebra.Projectivization
namespace BornVolume
export Projectivization (momentMap momentMap_sum_eq_one momentRatio_smul momentMap_mk
  momentMap_mk_eq_inner_sq)
end BornVolume


