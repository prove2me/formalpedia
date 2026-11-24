-- Prove2me | Definitions.Def_RequestProject_Theta
-- name    : RequestProject_Theta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T11:23:32.298368+00:00
-- url     : https://prove2.me/theorems/103a40e3-2a36-4c6d-8b0d-9301d0ff9751
-- title:
--   Theta
-- statement:
--   Definitions and structural lemmas for Theta, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theta.lean

import Definitions.Def_RequestProject_RecoverP
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
def pairMS : Sym2 ℕ → Multiset ℕ :=
  Sym2.lift ⟨fun a b => {a, b}, fun a b => Multiset.pair_comm a b⟩
def pairSum : Sym2 ℕ → ℕ := Sym2.lift ⟨fun a b => a + b, fun a b => Nat.add_comm a b⟩
def thetaAB (W : Multiset ℕ) (a b : ℕ) : MvPolynomial ℕ ℚ :=
  C ((a + b - 2 : ℕ) : ℚ) * mono ((a + b - 1) ::ₘ (W - {a, b})) + X (a + b) * fP (W - {a, b})
def theta (W : Multiset ℕ) : Sym2 ℕ → MvPolynomial ℕ ℚ :=
  Sym2.lift ⟨fun a b => thetaAB W a b, fun a b => by
    show thetaAB W a b = thetaAB W b a
    unfold thetaAB; rw [Multiset.pair_comm a b, Nat.add_comm a b]⟩
end ChromaticReconstruction


