-- Prove2me | Definitions.Def_BornVolumeLean_Volume_GaussianFS
-- name    : BornVolumeLean_Volume_GaussianFS
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:59:08.658249+00:00
-- url     : https://prove2.me/theorems/1c6956ef-288b-422b-a160-73f8f63eb33b
-- title:
--   Gaussian FS
-- statement:
--   Definitions and structural lemmas for Gaussian FS, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianFS.lean

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMeasurable
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
namespace BornVolume
variable {N : ℕ}
end BornVolume


