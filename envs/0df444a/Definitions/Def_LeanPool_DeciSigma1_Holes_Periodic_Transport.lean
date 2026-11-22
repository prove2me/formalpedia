-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
-- name    : LeanPool_DeciSigma1_Holes_Periodic_Transport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:41:35.089798+00:00
-- url     : https://prove2.me/theorems/2f988f5d-9588-4a21-b79b-ed7e8258721a
-- title:
--   Transport
-- statement:
--   Definitions and structural lemmas for Transport, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
def SuffixComparison (y : List α) (b : ℕ) (z : List α) (a : ℕ) : Prop :=
  ∀ n, b + n < y.length → y[b + n]? = z[a + n]?
namespace SuffixComparison
variable {y z : List α} {b a : ℕ}
end SuffixComparison
section Copy
variable [DecidableEq α] {V : Fin k → List α} {d : ℕ}
end Copy
section PieceCmp
variable [DecidableEq α] {W : Fin k → List α} {d : ℕ}
end PieceCmp
namespace AdmissibleDeletion
variable [DecidableEq α] {W : Fin k → List α} {ρ : List α} {N : ℕ} {x : Piece W ρ.length → ℕ}
def NoInteriorJunction (hx : AdmissibleDeletion W ρ N x) (l : Fin k) (c' m : ℕ) : Prop :=
  ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 → (hx.imagePiece R).start ≤ c' →
    c' < (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length → c' + m ≤
        (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length
variable (hx : AdmissibleDeletion W ρ N x)
include hx
omit [DecidableEq α] in
/-- Offsets `o` and `p` in pieces of period `d` carry the same states: they are equal, or both are
at least the transient length and agree modulo the state period. -/
def SameStatePhase (N d o p : ℕ) : Prop :=
  o = p ∨ (Periodic.stateTransientLength N d ≤ o ∧ Periodic.stateTransientLength N d ≤ p ∧
    o % Periodic.statePeriodModulus N d = p % Periodic.statePeriodModulus N d)
end AdmissibleDeletion
section Main
variable [DecidableEq α] {S : Type} [Fintype S] [DecidableEq S] {W : Fin k → List α}
  {ρ : List α} {x : Piece W ρ.length → ℕ}
end Main
section Holes
variable [DecidableEq α] {S : Type} [Fintype S] [DecidableEq S] {W : Fin k → List α}
  {ρ : List α} {x : Piece W ρ.length → ℕ}
section Site
variable {N dR : ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx
end Site
end Holes
end DeciSigma1.Holes.Periodic


