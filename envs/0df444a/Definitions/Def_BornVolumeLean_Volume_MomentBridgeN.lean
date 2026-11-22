-- Prove2me | Definitions.Def_BornVolumeLean_Volume_MomentBridgeN
-- name    : BornVolumeLean_Volume_MomentBridgeN
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:51:34.93233+00:00
-- url     : https://prove2.me/theorems/034ba3ff-c771-46eb-af6c-a9e6b7984377
-- title:
--   Moment Bridge N
-- statement:
--   Definitions and structural lemmas for Moment Bridge N, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentBridgeN.lean

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_PiCurry
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace BornVolume
noncomputable def gBlock : (Fin 2 → ℝ) → ℝ := fun w => (w 0) ^ 2 + (w 1) ^ 2
end BornVolume


