-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:44.763541+00:00
-- url     : https://prove2.me/theorems/6e4868b4-cdf5-41c4-9218-4d4f966dc2e8
-- title:
--   Gauss Sum Hermitian Norm Level Shift
-- statement:
--   Definitions and structural lemmas for Gauss Sum Hermitian Norm Level Shift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean

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
namespace GlobalTheory.CompanionTheory.GaussRec
variable {R : Type} [CommRing R]
def gaussTerm (σ : R →+* R) (ϖ : R) (hfix : σ ϖ = ϖ) (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ) (a : R)
    (k : ℕ) (w : R ⧸ lev ϖ k) : ℂ :=
  ψ k (Ideal.Quotient.mk (lev ϖ k) a * (barσ σ ϖ hfix k w * w))
def traceChar (σ : R →+* R) (ϖ : R) (hfix : σ ϖ = ϖ) (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ) (c : R) :
    AddChar (R ⧸ lev ϖ 1) ℂ :=
  (ψ 1).compAddMonoidHom (AddMonoidHom.mk'
    (fun t => Ideal.Quotient.mk (lev ϖ 1) c * t + barσ σ ϖ hfix 1 (Ideal.Quotient.mk (lev ϖ 1) c * t))
    (by intro x y; simp only [mul_add, map_add]; abel))
def lft (ϖ : R) (k : ℕ) (w : R ⧸ lev ϖ k) : R :=
  Function.surjInv (Ideal.Quotient.mk_surjective (I := lev ϖ k)) w
end GlobalTheory.CompanionTheory.GaussRec
end


