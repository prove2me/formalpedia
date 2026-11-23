-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:48.61334+00:00
-- url     : https://prove2.me/theorems/97b66308-8021-451a-a5ad-2693ec1a09e3
-- title:
--   Unimodular Hermitian Reps Count Succ
-- statement:
--   Definitions and structural lemmas for Unimodular Hermitian Reps Count Succ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnimodularHermitianRepsCountSucc.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Theorems.Thm_GlobalTheory_GramCount_Prim_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
namespace GlobalTheory.CompanionTheory.UnrDens.HenselStep
section Generic
end Generic
variable {R : Type} [CommRing R] {a b c : ℕ}
section Main
variable {σ : R →+* R} {ϖ : R}
abbrev solSet (σ : R →+* R) (ϖ : R) (S : Matrix (Fin a) (Fin a) R) (T : Matrix (Fin b) (Fin b) R)
    (k : ℕ) : Set (Matrix (Fin a) (Fin b) R) :=
  {x | red ϖ k (cT σ x * S * x) = red ϖ k T}
theorem lev_succ_le_lev (ϖ : R) (k : ℕ) : lev ϖ (k + 1) ≤ lev ϖ k :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (Nat.le_succ k))
def proj (ϖ : R) (k : ℕ) (t : Matrix (Fin a) (Fin b) (R ⧸ lev ϖ (k + 1))) :
    Matrix (Fin a) (Fin b) (R ⧸ lev ϖ k) :=
  t.map (Ideal.Quotient.factor (lev_succ_le_lev ϖ k))
theorem proj_red (ϖ : R) (k : ℕ) (x : Matrix (Fin a) (Fin b) R) :
    proj ϖ k (red ϖ (k + 1) x) = red ϖ k x := by
  ext i j; simp [proj, red]
theorem solSet_succ {S : Matrix (Fin a) (Fin a) R} {T : Matrix (Fin b) (Fin b) R} {k : ℕ}
    {x : Matrix (Fin a) (Fin b) R} (hx : x ∈ solSet σ ϖ S T (k + 1)) : x ∈ solSet σ ϖ S T k := by
  have h1 := congrArg (proj ϖ k) hx
  simp only [proj_red] at h1
  exact h1
def down (σ : R →+* R) (ϖ : R) (S : Matrix (Fin a) (Fin a) R) (T : Matrix (Fin b) (Fin b) R) (k : ℕ)
    (t : red ϖ (k + 1) '' solSet σ ϖ S T (k + 1)) : red ϖ k '' solSet σ ϖ S T k :=
  ⟨proj ϖ k t.1, by
    obtain ⟨x, hx, e⟩ := t.2
    exact ⟨x, solSet_succ hx, by rw [← e, proj_red]⟩⟩
end Main
end GlobalTheory.CompanionTheory.UnrDens.HenselStep


