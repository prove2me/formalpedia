-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:13.901313+00:00
-- url     : https://prove2.me/theorems/29d22afa-2dfc-4510-8c9c-c2f0136107fa
-- title:
--   Matrix Induction Transvection Diagonal
-- statement:
--   Definitions and structural lemmas for Matrix Induction Transvection Diagonal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.Adelic.StableRangeOne
def elem (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] :
    Submonoid (Matrix ι ι R) :=
  Submonoid.closure ({T | ∃ i j c, i ≠ j ∧ T = Matrix.transvection i j c} ∪
    {T | ∃ D : ι → R, (∀ i, IsUnit (D i)) ∧ T = Matrix.diagonal D})
def rowOp {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (k : ι) (c : ι → R) : Matrix ι ι R :=
  1 + Matrix.of fun i j => if i = k then c j else 0
def colOp {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (k : ι) (c : ι → R) : Matrix ι ι R :=
  1 + Matrix.of fun i j => if j = k then c i else 0
def Fixed {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (A : Matrix ι ι R) : Prop :=
  ∀ i j, (i ∉ s ∨ j ∉ s) → A i j = (1 : Matrix ι ι R) i j
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne


