-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
-- name    : LeanPool_DeciSigma1_Holes_Periodic_Deletion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:44:04.310381+00:00
-- url     : https://prove2.me/theorems/2baa38eb-6c04-481a-bcc6-298a25bd0966
-- title:
--   Deletion
-- statement:
--   Definitions and structural lemmas for Deletion, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
section Constants
def stateTransientLength (N d : ℕ) : ℕ := N * d
def statePeriodModulus (N d : ℕ) : ℕ := d * N.factorial
def boundaryMargin (N d : ℕ) : ℕ := stateTransientLength N d + statePeriodModulus N d
def comparisonGap (N d : ℕ) : ℕ := 2 * boundaryMargin N d + statePeriodModulus N d
def fixedMargin (N d : ℕ) : ℕ := 6 * boundaryMargin N d + 2 * statePeriodModulus N d
def pieceLengthBound (N d h t : ℕ) : ℕ :=
  fixedMargin N d + statePeriodModulus N d + ((t + 1) * 2 ^ h - 1) *
    (comparisonGap N d + statePeriodModulus N d)
end Constants
section Edit
variable [DecidableEq α]
structure AdmissibleDeletion (W : Fin k → List α) (ρ : List α) (N : ℕ) (x : Piece W ρ.length → ℕ) :
    Prop where
  supp : ∀ P, x P ≠ 0 → P ∈ piecesOf W ρ
  long : ∀ P ∈ piecesOf W ρ, x P ≠ 0 → Periodic.fixedMargin N ρ.length +
      Periodic.statePeriodModulus N ρ.length * x P ≤ P.len
  near : ∀ P ∈ piecesOf W ρ, ∀ Q ∈ piecesOf W ρ, FollowerEdge P Q →
    P.len < Q.len + Periodic.comparisonGap N ρ.length → Q.len < P.len +
        Periodic.comparisonGap N ρ.length → x P = x Q
  far : ∀ P ∈ piecesOf W ρ, ∀ Q ∈ piecesOf W ρ, FollowerEdge P Q → P.len +
      Periodic.comparisonGap N ρ.length ≤ Q.len →
    P.len - Periodic.statePeriodModulus N ρ.length * x P + Periodic.comparisonGap N ρ.length ≤
        Q.len - Periodic.statePeriodModulus N ρ.length * x Q
variable (W : Fin k → List α) (ρ : List α) (N : ℕ) (x : Piece W ρ.length → ℕ)
def pieceDeletionSites (P : Piece W ρ.length) : Finset ℕ :=
  Finset.Ico (P.start + Periodic.boundaryMargin N ρ.length)
      (P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x P)
def deletedPositions (l : Fin k) : Finset ℕ :=
  ((piecesOf W ρ).filter (fun P => P.coordinate = l)).biUnion (pieceDeletionSites W ρ N x)
def editedTuple : Fin k → List α := fun l => deletePositions (W l) (deletedPositions W ρ N x l)
def keepCut (l : Fin k) (a : ℕ) : ℕ := retainedCount (deletedPositions W ρ N x l) a
variable {W ρ N x}
end Edit
end DeciSigma1.Holes.Periodic


