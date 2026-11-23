-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:32.03469+00:00
-- url     : https://prove2.me/theorems/abf708c2-f830-4c20-b7f5-6ddf5e5fa5ab
-- title:
--   Hermitian Matrix Diagonalizable
-- statement:
--   Definitions and structural lemmas for Hermitian Matrix Diagonalizable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianMatrixDiagonalizable.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
namespace GlobalTheory.CompanionTheory.HermDiag
variable {R : Type} [CommRing R]
def ct (σ : R →+* R) {a b : Type} (x : Matrix a b R) : Matrix b a R := (x.map σ).transpose
def Hm (σ : R →+* R) {ι : Type} (h : Matrix ι ι R) : Prop := ∀ i j, σ (h i j) = h j i
def Diagble (σ : R →+* R) {ι : Type} [Fintype ι] [DecidableEq ι] (h : Matrix ι ι R) : Prop :=
  ∃ (g g' : Matrix ι ι R) (d : ι → R), g * g' = 1 ∧ g' * g = 1 ∧ (∀ i, σ (d i) = d i) ∧
    ct σ g * h * g = Matrix.diagonal d
section basic
variable {σ : R →+* R} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
end basic
section local_ring
variable {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end local_ring
end GlobalTheory.CompanionTheory.HermDiag
end


