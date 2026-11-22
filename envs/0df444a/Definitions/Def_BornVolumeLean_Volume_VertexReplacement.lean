-- Prove2me | Definitions.Def_BornVolumeLean_Volume_VertexReplacement
-- name    : BornVolumeLean_Volume_VertexReplacement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:58:31.226794+00:00
-- url     : https://prove2.me/theorems/ba042f12-9ea9-418f-aaef-fe1540bf1f95
-- title:
--   Vertex Replacement
-- statement:
--   Definitions and structural lemmas for Vertex Replacement, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/VertexReplacement.lean

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Matrix.Adjugate
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory Matrix
open scoped LinearAlgebra.Projectivization
namespace BornVolume
variable {N : ℕ}
noncomputable def replaceMap (b : Fin N → ℝ) (i : Fin N) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  Matrix.toLin' ((1 : Matrix (Fin N) (Fin N) ℝ).updateCol i b)
section Apex
variable {M : ℕ}
noncomputable def apexLin (b : Fin M → ℝ) : (Fin M → ℝ) →ₗ[ℝ] (Fin M → ℝ) :=
  Matrix.toLin' (1 - Matrix.of (fun (k : Fin M) (_ : Fin M) => b k))
end Apex
end BornVolume


