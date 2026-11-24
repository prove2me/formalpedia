-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OmegaEquivInducedFibre
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OmegaEquivInducedFibre
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:44.105016+00:00
-- url     : https://prove2.me/theorems/d55cc317-a745-4a34-be2f-4cbbbbf8d722
-- title:
--   Omega Equiv Induced Fibre
-- statement:
--   Definitions and structural lemmas for Omega Equiv Induced Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/OmegaEquivInducedFibre.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
namespace GlobalTheory.CompanionTheory.ThetaGLLen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]
def topR (e : c ⊕ d ≃ b) (y : Matrix c a k) : Matrix b a k := (fromRows y 0).submatrix e.symm id
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
@[simp] theorem topR_inl (e : c ⊕ d ≃ b) (y : Matrix c a k) (i : c) (l : a) :
    topR e y (e (.inl i)) l = y i l := by
  simp [topR]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
@[simp] theorem topR_inr (e : c ⊕ d ≃ b) (y : Matrix c a k) (i : d) (l : a) :
    topR e y (e (.inr i)) l = 0 := by
  simp [topR]
theorem rank_topR (e : c ⊕ d ≃ b) (y : Matrix c a k) : (topR e y).rank = y.rank := by
  refine le_antisymm ?_ ?_
  · have h : topR e y = ((1 : Matrix b b k).submatrix id fun i => e (.inl i)) * y := by
      ext i l
      obtain ⟨i | i, rfl⟩ := e.surjective i
      · simp [mul_apply, one_apply]
      · simp [mul_apply, one_apply]
    rw [h]
    exact rank_mul_le_right _ _
  · have h : (topR e y).submatrix (fun i => e (.inl i)) (Equiv.refl a) = y := by
      ext i l; simp
    have h2 := rank_submatrix_le (topR e y) (fun i => e (.inl i)) (Equiv.refl a)
    rwa [h] at h2
def topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} (y : RankIn k a c {κ}) : RankIn k a b {κ} :=
  ⟨topR e y.1, (rank_topR e y.1).trans y.2⟩
end GlobalTheory.CompanionTheory.ThetaGLLen


