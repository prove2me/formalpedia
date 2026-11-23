-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:01.644701+00:00
-- url     : https://prove2.me/theorems/b7b8cf20-8b1e-490c-bfab-d8fb0a583630
-- title:
--   Blk Conj Transpose
-- statement:
--   Definitions and structural lemmas for Blk Conj Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.AdmGL
variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}
def atPlace (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) : Matrix (Fin a) (Fin a) ℂ :=
  M.map fun x => x w
def blk (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex e e (blockDiagonal (atPlace M))
def unblk (e : Fin a × ι ≃ Fin n) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin a) (Fin a) (ι → ℂ) :=
  Matrix.of fun p q w => g (e (p, w)) (e (q, w))
def blkG (e : Fin a × ι ≃ Fin n) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  blk e '' {M | IsUnit M}
end GlobalTheory.CompanionTheory.AdmGL
end


