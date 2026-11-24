-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PTwinFdegNeZero
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PTwinFdegNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:30.756462+00:00
-- url     : https://prove2.me/theorems/c70b7935-c1b8-4721-a2b7-48e04c89cec8
-- title:
--   PTwin Fdeg Ne Zero
-- statement:
--   Definitions and structural lemmas for PTwin Fdeg Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PTwinFdegNeZero.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
open MvPolynomial Matrix Equiv
namespace FdegNeZero
variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}
def colExp (j N : ℕ) (l : Fin N) : ℕ := if (l : ℕ) < j then j - 1 - l else N - 1 - l
def blkMat (j : ℕ) (τ : Ψ) : Matrix (Fin N) (Fin N) (Rts Ψ N) :=
  Matrix.of fun i l => if ((i : ℕ) < j ↔ (l : ℕ) < j) then X (τ, i) ^ colExp j N l else 0
def bigMat (j : ℕ) : Matrix (Ψ × Fin N) (Ψ × Fin N) (Rts Ψ N) :=
  Matrix.of fun x l => if x.1 = l.1 ∧ ((x.2 : ℕ) < j ↔ (l.2 : ℕ) < j) then X x ^ colExp j N l.2 else 0
def rev (j : ℕ) (hj : j ≤ N) (i : Fin N) : Fin N :=
  ⟨if (i : ℕ) < j then j - 1 - i else N - 1 + j - i, by split_ifs <;> omega⟩
theorem rev_rev (j : ℕ) (hj : j ≤ N) (i : Fin N) : rev j hj (rev j hj i) = i := by
  apply Fin.ext
  simp only [rev]
  split_ifs <;> omega
def rho (j : ℕ) (hj : j ≤ N) : Perm (Ψ × Fin N) :=
  Function.Involutive.toPerm (fun x => (x.1, rev j hj x.2)) fun x => by simp [rev_rev]
end FdegNeZero
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine


